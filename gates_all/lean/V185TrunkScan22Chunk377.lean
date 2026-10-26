import V185TrunkScan22Chunk376

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3361725 : List Nat := [1, 4, 1, 2, 4, 1, 3, 1, 2, 3]
def baseStart_3361725 : Nat := 118140960795 + 3361725 * 2 ^ 59
def prefixEnd_3361725 : Nat := 4983230072969 + 3 ^ 40 * 3361725 * 2
def baseEnd_3361725 : Nat := 1150787168823976646118143

theorem tailTrace_3361725 : CollatzResearch.WordTrace tailWord_3361725 prefixEnd_3361725 1150787168823976646118143 := by
  unfold tailWord_3361725
  simp only [CollatzResearch.WordTrace]
  refine ⟨122612183746051936765734629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81741455830701291177156419 122612183746051936765734629)
  ·
    refine ⟨22989784452384738143575243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122612183746051936765734629 22989784452384738143575243)
    ·
      refine ⟨34484676678577107215362865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22989784452384738143575243 34484676678577107215362865)
      ·
        refine ⟨25863507508932830411522149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34484676678577107215362865 25863507508932830411522149)
        ·
          refine ⟨4849407657924905702160403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25863507508932830411522149 4849407657924905702160403)
          ·
            refine ⟨7274111486887358553240605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4849407657924905702160403 7274111486887358553240605)
            ·
              refine ⟨2727791807582759457465227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7274111486887358553240605 2727791807582759457465227)
              ·
                refine ⟨4091687711374139186197841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2727791807582759457465227 4091687711374139186197841)
                ·
                  refine ⟨3068765783530604389648381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4091687711374139186197841 3068765783530604389648381)
                  ·
                    refine ⟨1150787168823976646118143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3068765783530604389648381 1150787168823976646118143)
                    ·
                      rfl

theorem cell22_3361725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3, 1, 2, 3].length) (baseStart_3361725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3361725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3361725 prefixEnd_3361725 := by exact prefixLift 3361725
  have htrace : WordTrace (prefixWord ++ tailWord_3361725) baseStart_3361725 baseEnd_3361725 := by
    simpa [prefixWord, tailWord_3361725, baseEnd_3361725] using wordTrace_append hprefix tailTrace_3361725
  have hstable : (prefixWord ++ tailWord_3361725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361725).length < 2 ^ (prefixWord ++ tailWord_3361725).sum := by decide
  have hdescent : baseEnd_3361725 < baseStart_3361725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361764 : List Nat := [2, 3, 1, 1, 1, 1, 2, 4, 2, 5]
def baseStart_3361764 : Nat := 118140960795 + 3361764 * 2 ^ 59
def prefixEnd_3361764 : Nat := 4983230072969 + 3 ^ 40 * 3361764 * 2
def baseEnd_3361764 : Nat := 1150800519320993544393023

theorem tailTrace_3361764 : CollatzResearch.WordTrace tailWord_3361764 prefixEnd_3361764 1150800519320993544393023 := by
  unfold tailWord_3361764
  simp only [CollatzResearch.WordTrace]
  refine ⟨61306803096455323213202173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81742404128607097617602897 61306803096455323213202173)
  ·
    refine ⟨22990051161170746204950815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61306803096455323213202173 22990051161170746204950815)
    ·
      refine ⟨34485076741756119307426223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22990051161170746204950815 34485076741756119307426223)
      ·
        refine ⟨51727615112634178961139335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34485076741756119307426223 51727615112634178961139335)
        ·
          refine ⟨77591422668951268441709003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51727615112634178961139335 77591422668951268441709003)
          ·
            refine ⟨116387134003426902662563505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77591422668951268441709003 116387134003426902662563505)
            ·
              refine ⟨87290350502570176996922629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116387134003426902662563505 87290350502570176996922629)
              ·
                refine ⟨16366940719231908186922993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87290350502570176996922629 16366940719231908186922993)
                ·
                  refine ⟨12275205539423931140192245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16366940719231908186922993 12275205539423931140192245)
                  ·
                    refine ⟨1150800519320993544393023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12275205539423931140192245 1150800519320993544393023)
                    ·
                      rfl

theorem cell22_3361764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_3361764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3361764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3361764 prefixEnd_3361764 := by exact prefixLift 3361764
  have htrace : WordTrace (prefixWord ++ tailWord_3361764) baseStart_3361764 baseEnd_3361764 := by
    simpa [prefixWord, tailWord_3361764, baseEnd_3361764] using wordTrace_append hprefix tailTrace_3361764
  have hstable : (prefixWord ++ tailWord_3361764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361764).length < 2 ^ (prefixWord ++ tailWord_3361764).sum := by decide
  have hdescent : baseEnd_3361764 < baseStart_3361764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361811 : List Nat := [1, 1, 1, 2, 1, 4, 1, 7, 4]
def baseStart_3361811 : Nat := 118140960795 + 3361811 * 2 ^ 59
def prefixEnd_3361811 : Nat := 4983230072969 + 3 ^ 40 * 3361811 * 2
def baseEnd_3361811 : Nat := 383605536127167029489293

theorem tailTrace_3361811 : CollatzResearch.WordTrace tailWord_3361811 prefixEnd_3361811 383605536127167029489293 := by
  unfold tailWord_3361811
  simp only [CollatzResearch.WordTrace]
  refine ⟨122615320423740373453365287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81743546949160248968910191 122615320423740373453365287)
  ·
    refine ⟨183922980635610560180047931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122615320423740373453365287 183922980635610560180047931)
    ·
      refine ⟨275884470953415840270071897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183922980635610560180047931 275884470953415840270071897)
      ·
        refine ⟨206913353215061880202553923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275884470953415840270071897 206913353215061880202553923)
        ·
          refine ⟨310370029822592820303830885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206913353215061880202553923 310370029822592820303830885)
          ·
            refine ⟨58194380591736153806968291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 310370029822592820303830885 58194380591736153806968291)
            ·
              refine ⟨87291570887604230710452437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58194380591736153806968291 87291570887604230710452437)
              ·
                refine ⟨2045896192678224157276229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 87291570887604230710452437 2045896192678224157276229)
                ·
                  refine ⟨383605536127167029489293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2045896192678224157276229 383605536127167029489293)
                  ·
                    rfl

theorem cell22_3361811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 7, 4].length) (baseStart_3361811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3361811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3361811 prefixEnd_3361811 := by exact prefixLift 3361811
  have htrace : WordTrace (prefixWord ++ tailWord_3361811) baseStart_3361811 baseEnd_3361811 := by
    simpa [prefixWord, tailWord_3361811, baseEnd_3361811] using wordTrace_append hprefix tailTrace_3361811
  have hstable : (prefixWord ++ tailWord_3361811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361811).length < 2 ^ (prefixWord ++ tailWord_3361811).sum := by decide
  have hdescent : baseEnd_3361811 < baseStart_3361811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361856 : List Nat := [2, 1, 1, 2, 2, 3, 5, 6]
def baseStart_3361856 : Nat := 118140960795 + 3361856 * 2 ^ 59
def prefixEnd_3361856 : Nat := 4983230072969 + 3 ^ 40 * 3361856 * 2
def baseEnd_3361856 : Nat := 127870223644570663454749

theorem tailTrace_3361856 : CollatzResearch.WordTrace tailWord_3361856 prefixEnd_3361856 127870223644570663454749 := by
  unfold tailWord_3361856
  simp only [CollatzResearch.WordTrace]
  refine ⟨61308480854288673069376711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81744641139051564092502281 61308480854288673069376711)
  ·
    refine ⟨91962721281433009604065067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61308480854288673069376711 91962721281433009604065067)
    ·
      refine ⟨137944081922149514406097601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91962721281433009604065067 137944081922149514406097601)
      ·
        refine ⟨103458061441612135804573201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137944081922149514406097601 103458061441612135804573201)
        ·
          refine ⟨77593546081209101853429901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103458061441612135804573201 77593546081209101853429901)
          ·
            refine ⟨29097579780453413195036213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77593546081209101853429901 29097579780453413195036213)
            ·
              refine ⟨2727898104417507487034645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29097579780453413195036213 2727898104417507487034645)
              ·
                refine ⟨127870223644570663454749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2727898104417507487034645 127870223644570663454749)
                ·
                  rfl

theorem cell22_3361856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5, 6].length) (baseStart_3361856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3361856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3361856 prefixEnd_3361856 := by exact prefixLift 3361856
  have htrace : WordTrace (prefixWord ++ tailWord_3361856) baseStart_3361856 baseEnd_3361856 := by
    simpa [prefixWord, tailWord_3361856, baseEnd_3361856] using wordTrace_append hprefix tailTrace_3361856
  have hstable : (prefixWord ++ tailWord_3361856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361856).length < 2 ^ (prefixWord ++ tailWord_3361856).sum := by decide
  have hdescent : baseEnd_3361856 < baseStart_3361856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361862 : List Nat := [6, 1, 1, 1, 1, 3, 2, 3, 4]
def baseStart_3361862 : Nat := 118140960795 + 3361862 * 2 ^ 59
def prefixEnd_3361862 : Nat := 4983230072969 + 3 ^ 40 * 3361862 * 2
def baseEnd_3361862 : Nat := 383611355574584651814241

theorem tailTrace_3361862 : CollatzResearch.WordTrace tailWord_3361862 prefixEnd_3361862 383611355574584651814241 := by
  unfold tailWord_3361862
  simp only [CollatzResearch.WordTrace]
  refine ⟨3831786892079862786358495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 81744787031037072775647893 3831786892079862786358495)
  ·
    refine ⟨5747680338119794179537743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3831786892079862786358495 5747680338119794179537743)
    ·
      refine ⟨8621520507179691269306615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5747680338119794179537743 8621520507179691269306615)
      ·
        refine ⟨12932280760769536903959923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8621520507179691269306615 12932280760769536903959923)
        ·
          refine ⟨19398421141154305355939885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12932280760769536903959923 19398421141154305355939885)
          ·
            refine ⟨7274407927932864508477457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19398421141154305355939885 7274407927932864508477457)
            ·
              refine ⟨5455805945949648381358093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7274407927932864508477457 5455805945949648381358093)
              ·
                refine ⟨2045927229731118143009285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5455805945949648381358093 2045927229731118143009285)
                ·
                  refine ⟨383611355574584651814241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2045927229731118143009285 383611355574584651814241)
                  ·
                    rfl

theorem cell22_3361862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_3361862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3361862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3361862 prefixEnd_3361862 := by exact prefixLift 3361862
  have htrace : WordTrace (prefixWord ++ tailWord_3361862) baseStart_3361862 baseEnd_3361862 := by
    simpa [prefixWord, tailWord_3361862, baseEnd_3361862] using wordTrace_append hprefix tailTrace_3361862
  have hstable : (prefixWord ++ tailWord_3361862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361862).length < 2 ^ (prefixWord ++ tailWord_3361862).sum := by decide
  have hdescent : baseEnd_3361862 < baseStart_3361862 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361888 : List Nat := [2, 1, 1, 3, 2, 2, 4, 1, 3, 3]
def baseStart_3361888 : Nat := 118140960795 + 3361888 * 2 ^ 59
def prefixEnd_3361888 : Nat := 4983230072969 + 3 ^ 40 * 3361888 * 2
def baseEnd_3361888 : Nat := 1150842967055098554292643

theorem tailTrace_3361888 : CollatzResearch.WordTrace tailWord_3361888 prefixEnd_3361888 1150842967055098554292643 := by
  unfold tailWord_3361888
  simp only [CollatzResearch.WordTrace]
  refine ⟨61309064422230707801959159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81745419229640943735945545 61309064422230707801959159)
  ·
    refine ⟨91963596633346061702938739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61309064422230707801959159 91963596633346061702938739)
    ·
      refine ⟨137945394950019092554408109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91963596633346061702938739 137945394950019092554408109)
      ·
        refine ⟨51729523106257159707903041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137945394950019092554408109 51729523106257159707903041)
        ·
          refine ⟨38797142329692869780927281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51729523106257159707903041 38797142329692869780927281)
          ·
            refine ⟨29097856747269652335695461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38797142329692869780927281 29097856747269652335695461)
            ·
              refine ⟨5455848140113059812942899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29097856747269652335695461 5455848140113059812942899)
              ·
                refine ⟨8183772210169589719414349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5455848140113059812942899 8183772210169589719414349)
                ·
                  refine ⟨3068914578813596144780381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8183772210169589719414349 3068914578813596144780381)
                  ·
                    refine ⟨1150842967055098554292643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3068914578813596144780381 1150842967055098554292643)
                    ·
                      rfl

theorem cell22_3361888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 1, 3, 3].length) (baseStart_3361888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3361888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3361888 prefixEnd_3361888 := by exact prefixLift 3361888
  have htrace : WordTrace (prefixWord ++ tailWord_3361888) baseStart_3361888 baseEnd_3361888 := by
    simpa [prefixWord, tailWord_3361888, baseEnd_3361888] using wordTrace_append hprefix tailTrace_3361888
  have hstable : (prefixWord ++ tailWord_3361888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361888).length < 2 ^ (prefixWord ++ tailWord_3361888).sum := by decide
  have hdescent : baseEnd_3361888 < baseStart_3361888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361965 : List Nat := [1, 5, 2, 1, 3, 1, 1, 1, 3, 4]
def baseStart_3361965 : Nat := 118140960795 + 3361965 * 2 ^ 59
def prefixEnd_3361965 : Nat := 4983230072969 + 3 ^ 40 * 3361965 * 2
def baseEnd_3361965 : Nat := 1150869325728696020117407

theorem tailTrace_3361965 : CollatzResearch.WordTrace tailWord_3361965 prefixEnd_3361965 1150869325728696020117407 := by
  unfold tailWord_3361965
  simp only [CollatzResearch.WordTrace]
  refine ⟨122620937265182457754471349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81747291510121638502980899 122620937265182457754471349)
  ·
    refine ⟨11495712868610855414481689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 122620937265182457754471349 11495712868610855414481689)
    ·
      refine ⟨8621784651458141560861267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11495712868610855414481689 8621784651458141560861267)
      ·
        refine ⟨12932676977187212341291901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8621784651458141560861267 12932676977187212341291901)
        ·
          refine ⟨4849753866445204627984463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12932676977187212341291901 4849753866445204627984463)
          ·
            refine ⟨7274630799667806941976695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4849753866445204627984463 7274630799667806941976695)
            ·
              refine ⟨10911946199501710412965043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7274630799667806941976695 10911946199501710412965043)
              ·
                refine ⟨16367919299252565619447565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10911946199501710412965043 16367919299252565619447565)
                ·
                  refine ⟨6137969737219712107292837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16367919299252565619447565 6137969737219712107292837)
                  ·
                    refine ⟨1150869325728696020117407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6137969737219712107292837 1150869325728696020117407)
                    ·
                      rfl

theorem cell22_3361965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_3361965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3361965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3361965 prefixEnd_3361965 := by exact prefixLift 3361965
  have htrace : WordTrace (prefixWord ++ tailWord_3361965) baseStart_3361965 baseEnd_3361965 := by
    simpa [prefixWord, tailWord_3361965, baseEnd_3361965] using wordTrace_append hprefix tailTrace_3361965
  have hstable : (prefixWord ++ tailWord_3361965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361965).length < 2 ^ (prefixWord ++ tailWord_3361965).sum := by decide
  have hdescent : baseEnd_3361965 < baseStart_3361965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361982 : List Nat := [4, 2, 1, 1, 3, 2, 3, 1, 1, 4]
def baseStart_3361982 : Nat := 118140960795 + 3361982 * 2 ^ 59
def prefixEnd_3361982 : Nat := 4983230072969 + 3 ^ 40 * 3361982 * 2
def baseEnd_3361982 : Nat := 1150875145176113642442355

theorem tailTrace_3361982 : CollatzResearch.WordTrace tailWord_3361982 prefixEnd_3361982 1150875145176113642442355 := by
  unfold tailWord_3361982
  simp only [CollatzResearch.WordTrace]
  refine ⟨15327694663265108707230025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81747704870747246438560133 15327694663265108707230025)
  ·
    refine ⟨11495770997448831530422519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15327694663265108707230025 11495770997448831530422519)
    ·
      refine ⟨17243656496173247295633779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11495770997448831530422519 17243656496173247295633779)
      ·
        refine ⟨25865484744259870943450669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17243656496173247295633779 25865484744259870943450669)
        ·
          refine ⟨9699556779097451603794001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25865484744259870943450669 9699556779097451603794001)
          ·
            refine ⟨7274667584323088702845501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9699556779097451603794001 7274667584323088702845501)
            ·
              refine ⟨2728000344121158263567063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7274667584323088702845501 2728000344121158263567063)
              ·
                refine ⟨4092000516181737395350595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2728000344121158263567063 4092000516181737395350595)
                ·
                  refine ⟨6138000774272606093025893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4092000516181737395350595 6138000774272606093025893)
                  ·
                    refine ⟨1150875145176113642442355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6138000774272606093025893 1150875145176113642442355)
                    ·
                      rfl

theorem cell22_3361982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3, 1, 1, 4].length) (baseStart_3361982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3361982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3361982 prefixEnd_3361982 := by exact prefixLift 3361982
  have htrace : WordTrace (prefixWord ++ tailWord_3361982) baseStart_3361982 baseEnd_3361982 := by
    simpa [prefixWord, tailWord_3361982, baseEnd_3361982] using wordTrace_append hprefix tailTrace_3361982
  have hstable : (prefixWord ++ tailWord_3361982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361982).length < 2 ^ (prefixWord ++ tailWord_3361982).sum := by decide
  have hdescent : baseEnd_3361982 < baseStart_3361982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361990 : List Nat := [6, 1, 2, 2, 1, 2, 2, 2, 1, 3]
def baseStart_3361990 : Nat := 118140960795 + 3361990 * 2 ^ 59
def prefixEnd_3361990 : Nat := 4983230072969 + 3 ^ 40 * 3361990 * 2
def baseEnd_3361990 : Nat := 1150877883739604288242331

theorem tailTrace_3361990 : CollatzResearch.WordTrace tailWord_3361990 prefixEnd_3361990 1150877883739604288242331 := by
  unfold tailWord_3361990
  simp only [CollatzResearch.WordTrace]
  refine ⟨3831932784065371469504107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 81747899393394591349420949 3831932784065371469504107)
  ·
    refine ⟨5747899176098057204256161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3831932784065371469504107 5747899176098057204256161)
    ·
      refine ⟨4310924382073542903192121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5747899176098057204256161 4310924382073542903192121)
      ·
        refine ⟨3233193286555157177394091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4310924382073542903192121 3233193286555157177394091)
        ·
          refine ⟨4849789929832735766091137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3233193286555157177394091 4849789929832735766091137)
          ·
            refine ⟨3637342447374551824568353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4849789929832735766091137 3637342447374551824568353)
            ·
              refine ⟨2728006835530913868426265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3637342447374551824568353 2728006835530913868426265)
              ·
                refine ⟨2046005126648185401319699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2728006835530913868426265 2046005126648185401319699)
                ·
                  refine ⟨3069007689972278101979549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2046005126648185401319699 3069007689972278101979549)
                  ·
                    refine ⟨1150877883739604288242331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3069007689972278101979549 1150877883739604288242331)
                    ·
                      rfl

theorem cell22_3361990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_3361990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3361990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3361990 prefixEnd_3361990 := by exact prefixLift 3361990
  have htrace : WordTrace (prefixWord ++ tailWord_3361990) baseStart_3361990 baseEnd_3361990 := by
    simpa [prefixWord, tailWord_3361990, baseEnd_3361990] using wordTrace_append hprefix tailTrace_3361990
  have hstable : (prefixWord ++ tailWord_3361990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361990).length < 2 ^ (prefixWord ++ tailWord_3361990).sum := by decide
  have hdescent : baseEnd_3361990 < baseStart_3361990 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362128 : List Nat := [2, 1, 1, 1, 1, 5, 1, 2, 4, 4]
def baseStart_3362128 : Nat := 118140960795 + 3362128 * 2 ^ 59
def prefixEnd_3362128 : Nat := 4983230072969 + 3 ^ 40 * 3362128 * 2
def baseEnd_3362128 : Nat := 1150925123959817928291907

theorem tailTrace_3362128 : CollatzResearch.WordTrace tailWord_3362128 prefixEnd_3362128 1150925123959817928291907 := by
  unfold tailWord_3362128
  simp only [CollatzResearch.WordTrace]
  refine ⟨61313441181795968296327519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81751254909061291061770025 61313441181795968296327519)
  ·
    refine ⟨91970161772693952444491279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61313441181795968296327519 91970161772693952444491279)
    ·
      refine ⟨137955242659040928666736919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91970161772693952444491279 137955242659040928666736919)
      ·
        refine ⟨206932863988561393000105379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137955242659040928666736919 206932863988561393000105379)
        ·
          refine ⟨310399295982842089500158069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206932863988561393000105379 310399295982842089500158069)
          ·
            refine ⟨29099933998391445890639819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 310399295982842089500158069 29099933998391445890639819)
            ·
              refine ⟨43649900997587168835959729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29099933998391445890639819 43649900997587168835959729)
              ·
                refine ⟨32737425748190376626969797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43649900997587168835959729 32737425748190376626969797)
                ·
                  refine ⟨6138267327785695617556837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32737425748190376626969797 6138267327785695617556837)
                  ·
                    refine ⟨1150925123959817928291907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6138267327785695617556837 1150925123959817928291907)
                    ·
                      rfl

theorem cell22_3362128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 4, 4].length) (baseStart_3362128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3362128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3362128 prefixEnd_3362128 := by exact prefixLift 3362128
  have htrace : WordTrace (prefixWord ++ tailWord_3362128) baseStart_3362128 baseEnd_3362128 := by
    simpa [prefixWord, tailWord_3362128, baseEnd_3362128] using wordTrace_append hprefix tailTrace_3362128
  have hstable : (prefixWord ++ tailWord_3362128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362128).length < 2 ^ (prefixWord ++ tailWord_3362128).sum := by decide
  have hdescent : baseEnd_3362128 < baseStart_3362128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362173 : List Nat := [1, 4, 1, 1, 2, 2, 1, 1, 1, 8]
def baseStart_3362173 : Nat := 118140960795 + 3362173 * 2 ^ 59
def prefixEnd_3362173 : Nat := 4983230072969 + 3 ^ 40 * 3362173 * 2
def baseEnd_3362173 : Nat := 1150940528379452810916769

theorem tailTrace_3362173 : CollatzResearch.WordTrace tailWord_3362173 prefixEnd_3362173 1150940528379452810916769 := by
  unfold tailWord_3362173
  simp only [CollatzResearch.WordTrace]
  refine ⟨122628523648428909278043173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81752349098952606185362115 122628523648428909278043173)
  ·
    refine ⟨22992848184080420489633095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122628523648428909278043173 22992848184080420489633095)
    ·
      refine ⟨34489272276120630734449643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22992848184080420489633095 34489272276120630734449643)
      ·
        refine ⟨51733908414180946101674465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34489272276120630734449643 51733908414180946101674465)
        ·
          refine ⟨38800431310635709576255849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51733908414180946101674465 38800431310635709576255849)
          ·
            refine ⟨29100323482976782182191887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38800431310635709576255849 29100323482976782182191887)
            ·
              refine ⟨43650485224465173273287831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29100323482976782182191887 43650485224465173273287831)
              ·
                refine ⟨65475727836697759909931747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43650485224465173273287831 65475727836697759909931747)
                ·
                  refine ⟨98213591755046639864897621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65475727836697759909931747 98213591755046639864897621)
                  ·
                    refine ⟨1150940528379452810916769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 98213591755046639864897621 1150940528379452810916769)
                    ·
                      rfl

theorem cell22_3362173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_3362173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3362173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3362173 prefixEnd_3362173 := by exact prefixLift 3362173
  have htrace : WordTrace (prefixWord ++ tailWord_3362173) baseStart_3362173 baseEnd_3362173 := by
    simpa [prefixWord, tailWord_3362173, baseEnd_3362173] using wordTrace_append hprefix tailTrace_3362173
  have hstable : (prefixWord ++ tailWord_3362173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362173).length < 2 ^ (prefixWord ++ tailWord_3362173).sum := by decide
  have hdescent : baseEnd_3362173 < baseStart_3362173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362177 : List Nat := [1, 2, 4, 3, 2, 2, 1, 7]
def baseStart_3362177 : Nat := 118140960795 + 3362177 * 2 ^ 59
def prefixEnd_3362177 : Nat := 4983230072969 + 3 ^ 40 * 3362177 * 2
def baseEnd_3362177 : Nat := 127882433073466459312973

theorem tailTrace_3362177 : CollatzResearch.WordTrace tailWord_3362177 prefixEnd_3362177 127882433073466459312973 := by
  unfold tailWord_3362177
  simp only [CollatzResearch.WordTrace]
  refine ⟨122628669540414417961188785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81752446360276278640792523 122628669540414417961188785)
  ·
    refine ⟨91971502155310813470891589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122628669540414417961188785 91971502155310813470891589)
    ·
      refine ⟨17244656654120777525792173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91971502155310813470891589 17244656654120777525792173)
      ·
        refine ⟨6466746245295291572172065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17244656654120777525792173 6466746245295291572172065)
        ·
          refine ⟨4850059683971468679129049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6466746245295291572172065 4850059683971468679129049)
          ·
            refine ⟨3637544762978601509346787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4850059683971468679129049 3637544762978601509346787)
            ·
              refine ⟨5456317144467902264020181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3637544762978601509346787 5456317144467902264020181)
              ·
                refine ⟨127882433073466459312973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5456317144467902264020181 127882433073466459312973)
                ·
                  rfl

theorem cell22_3362177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 7].length) (baseStart_3362177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3362177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3362177 prefixEnd_3362177 := by exact prefixLift 3362177
  have htrace : WordTrace (prefixWord ++ tailWord_3362177) baseStart_3362177 baseEnd_3362177 := by
    simpa [prefixWord, tailWord_3362177, baseEnd_3362177] using wordTrace_append hprefix tailTrace_3362177
  have hstable : (prefixWord ++ tailWord_3362177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362177).length < 2 ^ (prefixWord ++ tailWord_3362177).sum := by decide
  have hdescent : baseEnd_3362177 < baseStart_3362177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362194 : List Nat := [3, 2, 3, 3, 1, 1, 3, 6]
def baseStart_3362194 : Nat := 118140960795 + 3362194 * 2 ^ 59
def prefixEnd_3362194 : Nat := 4983230072969 + 3 ^ 40 * 3362194 * 2
def baseEnd_3362194 : Nat := 127883079678735084015745

theorem tailTrace_3362194 : CollatzResearch.WordTrace tailWord_3362194 prefixEnd_3362194 127883079678735084015745 := by
  unfold tailWord_3362194
  simp only [CollatzResearch.WordTrace]
  refine ⟨30657322395338207466139409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81752859720901886576371757 30657322395338207466139409)
  ·
    refine ⟨22992991796503655599604557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30657322395338207466139409 22992991796503655599604557)
    ·
      refine ⟨8622371923688870849851709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22992991796503655599604557 8622371923688870849851709)
      ·
        refine ⟨3233389471383326568694391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8622371923688870849851709 3233389471383326568694391)
        ·
          refine ⟨4850084207074989853041587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3233389471383326568694391 4850084207074989853041587)
          ·
            refine ⟨7275126310612484779562381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4850084207074989853041587 7275126310612484779562381)
            ·
              refine ⟨2728172366479681792335893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7275126310612484779562381 2728172366479681792335893)
              ·
                refine ⟨127883079678735084015745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2728172366479681792335893 127883079678735084015745)
                ·
                  rfl

theorem cell22_3362194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3, 6].length) (baseStart_3362194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3362194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3362194 prefixEnd_3362194 := by exact prefixLift 3362194
  have htrace : WordTrace (prefixWord ++ tailWord_3362194) baseStart_3362194 baseEnd_3362194 := by
    simpa [prefixWord, tailWord_3362194, baseEnd_3362194] using wordTrace_append hprefix tailTrace_3362194
  have hstable : (prefixWord ++ tailWord_3362194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362194).length < 2 ^ (prefixWord ++ tailWord_3362194).sum := by decide
  have hdescent : baseEnd_3362194 < baseStart_3362194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362250 : List Nat := [3, 1, 2, 1, 2, 3, 2, 2, 6]
def baseStart_3362250 : Nat := 118140960795 + 3362250 * 2 ^ 59
def prefixEnd_3362250 : Nat := 4983230072969 + 3 ^ 40 * 3362250 * 2
def baseEnd_3362250 : Nat := 383655629017683425580511

theorem tailTrace_3362250 : CollatzResearch.WordTrace tailWord_3362250 prefixEnd_3362250 383655629017683425580511 := by
  unfold tailWord_3362250
  simp only [CollatzResearch.WordTrace]
  refine ⟨30657833017287487857149051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81754221379433300952397469 30657833017287487857149051)
  ·
    refine ⟨45986749525931231785723577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30657833017287487857149051 45986749525931231785723577)
    ·
      refine ⟨34490062144448423839292683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45986749525931231785723577 34490062144448423839292683)
      ·
        refine ⟨51735093216672635758939025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34490062144448423839292683 51735093216672635758939025)
        ·
          refine ⟨38801319912504476819204269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51735093216672635758939025 38801319912504476819204269)
          ·
            refine ⟨14550494967189178807201601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38801319912504476819204269 14550494967189178807201601)
            ·
              refine ⟨10912871225391884105401201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14550494967189178807201601 10912871225391884105401201)
              ·
                refine ⟨8184653419043913079050901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10912871225391884105401201 8184653419043913079050901)
                ·
                  refine ⟨383655629017683425580511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8184653419043913079050901 383655629017683425580511)
                  ·
                    rfl

theorem cell22_3362250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2, 6].length) (baseStart_3362250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3362250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3362250 prefixEnd_3362250 := by exact prefixLift 3362250
  have htrace : WordTrace (prefixWord ++ tailWord_3362250) baseStart_3362250 baseEnd_3362250 := by
    simpa [prefixWord, tailWord_3362250, baseEnd_3362250] using wordTrace_append hprefix tailTrace_3362250
  have hstable : (prefixWord ++ tailWord_3362250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362250).length < 2 ^ (prefixWord ++ tailWord_3362250).sum := by decide
  have hdescent : baseEnd_3362250 < baseStart_3362250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362252 : List Nat := [2, 2, 1, 4, 2, 1, 1, 4, 1, 4]
def baseStart_3362252 : Nat := 118140960795 + 3362252 * 2 ^ 59
def prefixEnd_3362252 : Nat := 4983230072969 + 3 ^ 40 * 3362252 * 2
def baseEnd_3362252 : Nat := 1150967571693922938191527

theorem tailTrace_3362252 : CollatzResearch.WordTrace tailWord_3362252 prefixEnd_3362252 1150967571693922938191527 := by
  unfold tailWord_3362252
  simp only [CollatzResearch.WordTrace]
  refine ⟨61315702507571352885084505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81754270010095137180112673 61315702507571352885084505)
  ·
    refine ⟨45986776880678514663813379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61315702507571352885084505 45986776880678514663813379)
    ·
      refine ⟨68980165321017771995720069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45986776880678514663813379 68980165321017771995720069)
      ·
        refine ⟨12933780997690832249197513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68980165321017771995720069 12933780997690832249197513)
        ·
          refine ⟨9700335748268124186898135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12933780997690832249197513 9700335748268124186898135)
          ·
            refine ⟨14550503622402186280347203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9700335748268124186898135 14550503622402186280347203)
            ·
              refine ⟨21825755433603279420520805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14550503622402186280347203 21825755433603279420520805)
              ·
                refine ⟨4092329143800614891347651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21825755433603279420520805 4092329143800614891347651)
                ·
                  refine ⟨6138493715700922337021477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4092329143800614891347651 6138493715700922337021477)
                  ·
                    refine ⟨1150967571693922938191527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6138493715700922337021477 1150967571693922938191527)
                    ·
                      rfl

theorem cell22_3362252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 4, 1, 4].length) (baseStart_3362252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3362252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3362252 prefixEnd_3362252 := by exact prefixLift 3362252
  have htrace : WordTrace (prefixWord ++ tailWord_3362252) baseStart_3362252 baseEnd_3362252 := by
    simpa [prefixWord, tailWord_3362252, baseEnd_3362252] using wordTrace_append hprefix tailTrace_3362252
  have hstable : (prefixWord ++ tailWord_3362252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362252).length < 2 ^ (prefixWord ++ tailWord_3362252).sum := by decide
  have hdescent : baseEnd_3362252 < baseStart_3362252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362355 : List Nat := [1, 1, 1, 2, 4, 3, 1, 1, 1, 7]
def baseStart_3362355 : Nat := 118140960795 + 3362355 * 2 ^ 59
def prefixEnd_3362355 : Nat := 4983230072969 + 3 ^ 40 * 3362355 * 2
def baseEnd_3362355 : Nat := 1151002830698865002866211

theorem tailTrace_3362355 : CollatzResearch.WordTrace tailWord_3362355 prefixEnd_3362355 1151002830698865002866211 := by
  unfold tailWord_3362355
  simp only [CollatzResearch.WordTrace]
  refine ⟨122635161733769554361168519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81756774489179702907445679 122635161733769554361168519)
  ·
    refine ⟨183952742600654331541752779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122635161733769554361168519 183952742600654331541752779)
    ·
      refine ⟨275929113900981497312629169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183952742600654331541752779 275929113900981497312629169)
      ·
        refine ⟨206946835425736122984471877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275929113900981497312629169 206946835425736122984471877)
        ·
          refine ⟨38802531642325523059588477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 206946835425736122984471877 38802531642325523059588477)
          ·
            refine ⟨14550949365872071147345679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38802531642325523059588477 14550949365872071147345679)
            ·
              refine ⟨21826424048808106721018519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14550949365872071147345679 21826424048808106721018519)
              ·
                refine ⟨32739636073212160081527779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21826424048808106721018519 32739636073212160081527779)
                ·
                  refine ⟨49109454109818240122291669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32739636073212160081527779 49109454109818240122291669)
                  ·
                    refine ⟨1151002830698865002866211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49109454109818240122291669 1151002830698865002866211)
                    ·
                      rfl

theorem cell22_3362355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 7].length) (baseStart_3362355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3362355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3362355 prefixEnd_3362355 := by exact prefixLift 3362355
  have htrace : WordTrace (prefixWord ++ tailWord_3362355) baseStart_3362355 baseEnd_3362355 := by
    simpa [prefixWord, tailWord_3362355, baseEnd_3362355] using wordTrace_append hprefix tailTrace_3362355
  have hstable : (prefixWord ++ tailWord_3362355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362355).length < 2 ^ (prefixWord ++ tailWord_3362355).sum := by decide
  have hdescent : baseEnd_3362355 < baseStart_3362355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362357 : List Nat := [1, 3, 3, 1, 1, 3, 2, 3, 5]
def baseStart_3362357 : Nat := 118140960795 + 3362357 * 2 ^ 59
def prefixEnd_3362357 : Nat := 4983230072969 + 3 ^ 40 * 3362357 * 2
def baseEnd_3362357 : Nat := 383667838446579221438735

theorem tailTrace_3362357 : CollatzResearch.WordTrace tailWord_3362357 prefixEnd_3362357 383667838446579221438735 := by
  unfold tailWord_3362357
  simp only [CollatzResearch.WordTrace]
  refine ⟨122635234679762308702741325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81756823119841539135160883 122635234679762308702741325)
  ·
    refine ⟨45988213004910865763527997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122635234679762308702741325 45988213004910865763527997)
    ·
      refine ⟨17245579876841574661322999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45988213004910865763527997 17245579876841574661322999)
      ·
        refine ⟨25868369815262361991984499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17245579876841574661322999 25868369815262361991984499)
        ·
          refine ⟨38802554722893542987976749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25868369815262361991984499 38802554722893542987976749)
          ·
            refine ⟨14550958021085078620491281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38802554722893542987976749 14550958021085078620491281)
            ·
              refine ⟨10913218515813808965368461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14550958021085078620491281 10913218515813808965368461)
              ·
                refine ⟨4092456943430178362013173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10913218515813808965368461 4092456943430178362013173)
                ·
                  refine ⟨383667838446579221438735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4092456943430178362013173 383667838446579221438735)
                  ·
                    rfl

theorem cell22_3362357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 3, 5].length) (baseStart_3362357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3362357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3362357 prefixEnd_3362357 := by exact prefixLift 3362357
  have htrace : WordTrace (prefixWord ++ tailWord_3362357) baseStart_3362357 baseEnd_3362357 := by
    simpa [prefixWord, tailWord_3362357, baseEnd_3362357] using wordTrace_append hprefix tailTrace_3362357
  have hstable : (prefixWord ++ tailWord_3362357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362357).length < 2 ^ (prefixWord ++ tailWord_3362357).sum := by decide
  have hdescent : baseEnd_3362357 < baseStart_3362357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362385 : List Nat := [1, 2, 2, 1, 3, 2, 1, 2, 8]
def baseStart_3362385 : Nat := 118140960795 + 3362385 * 2 ^ 59
def prefixEnd_3362385 : Nat := 4983230072969 + 3 ^ 40 * 3362385 * 2
def baseEnd_3362385 : Nat := 383671033437318308205373

theorem tailTrace_3362385 : CollatzResearch.WordTrace tailWord_3362385 prefixEnd_3362385 383671033437318308205373 := by
  unfold tailWord_3362385
  simp only [CollatzResearch.WordTrace]
  refine ⟨122636255923660869484760609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81757503949107246323173739 122636255923660869484760609)
  ·
    refine ⟨91977191942745652113570457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122636255923660869484760609 91977191942745652113570457)
    ·
      refine ⟨68982893957059239085177843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91977191942745652113570457 68982893957059239085177843)
      ·
        refine ⟨103474340935588858627766765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68982893957059239085177843 103474340935588858627766765)
        ·
          refine ⟨38802877850845821985412537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103474340935588858627766765 38802877850845821985412537)
          ·
            refine ⟨29102158388134366489059403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38802877850845821985412537 29102158388134366489059403)
            ·
              refine ⟨43653237582201549733589105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29102158388134366489059403 43653237582201549733589105)
              ·
                refine ⟨32739928186651162300191829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43653237582201549733589105 32739928186651162300191829)
                ·
                  refine ⟨383671033437318308205373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32739928186651162300191829 383671033437318308205373)
                  ·
                    rfl

theorem cell22_3362385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 8].length) (baseStart_3362385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3362385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3362385 prefixEnd_3362385 := by exact prefixLift 3362385
  have htrace : WordTrace (prefixWord ++ tailWord_3362385) baseStart_3362385 baseEnd_3362385 := by
    simpa [prefixWord, tailWord_3362385, baseEnd_3362385] using wordTrace_append hprefix tailTrace_3362385
  have hstable : (prefixWord ++ tailWord_3362385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362385).length < 2 ^ (prefixWord ++ tailWord_3362385).sum := by decide
  have hdescent : baseEnd_3362385 < baseStart_3362385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362421 : List Nat := [1, 3, 4, 2, 1, 2, 2, 2, 1, 4]
def baseStart_3362421 : Nat := 118140960795 + 3362421 * 2 ^ 59
def prefixEnd_3362421 : Nat := 4983230072969 + 3 ^ 40 * 3362421 * 2
def baseEnd_3362421 : Nat := 1151025423847662830716009

theorem tailTrace_3362421 : CollatzResearch.WordTrace tailWord_3362421 prefixEnd_3362421 1151025423847662830716009 := by
  unfold tailWord_3362421
  simp only [CollatzResearch.WordTrace]
  refine ⟨122637568951530447633071117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81758379301020298422047411 122637568951530447633071117)
  ·
    refine ⟨45989088356823917862401669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122637568951530447633071117 45989088356823917862401669)
    ·
      refine ⟨8622954066904484599200313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45989088356823917862401669 8622954066904484599200313)
      ·
        refine ⟨6467215550178363449400235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8622954066904484599200313 6467215550178363449400235)
        ·
          refine ⟨9700823325267545174100353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6467215550178363449400235 9700823325267545174100353)
          ·
            refine ⟨7275617493950658880575265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9700823325267545174100353 7275617493950658880575265)
            ·
              refine ⟨5456713120462994160431449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7275617493950658880575265 5456713120462994160431449)
              ·
                refine ⟨4092534840347245620323587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5456713120462994160431449 4092534840347245620323587)
                ·
                  refine ⟨6138802260520868430485381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4092534840347245620323587 6138802260520868430485381)
                  ·
                    refine ⟨1151025423847662830716009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6138802260520868430485381 1151025423847662830716009)
                    ·
                      rfl

theorem cell22_3362421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_3362421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3362421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3362421 prefixEnd_3362421 := by exact prefixLift 3362421
  have htrace : WordTrace (prefixWord ++ tailWord_3362421) baseStart_3362421 baseEnd_3362421 := by
    simpa [prefixWord, tailWord_3362421, baseEnd_3362421] using wordTrace_append hprefix tailTrace_3362421
  have hstable : (prefixWord ++ tailWord_3362421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362421).length < 2 ^ (prefixWord ++ tailWord_3362421).sum := by decide
  have hdescent : baseEnd_3362421 < baseStart_3362421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362432 : List Nat := [2, 1, 1, 2, 1, 4, 2, 3, 2, 4]
def baseStart_3362432 : Nat := 118140960795 + 3362432 * 2 ^ 59
def prefixEnd_3362432 : Nat := 4983230072969 + 3 ^ 40 * 3362432 * 2
def baseEnd_3362432 : Nat := 1151029189372462468690975

theorem tailTrace_3362432 : CollatzResearch.WordTrace tailWord_3362432 prefixEnd_3362432 1151029189372462468690975 := by
  unfold tailWord_3362432
  simp only [CollatzResearch.WordTrace]
  refine ⟨61318985077245298255860775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81758646769660397674481033 61318985077245298255860775)
  ·
    refine ⟨91978477615867947383791163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61318985077245298255860775 91978477615867947383791163)
    ·
      refine ⟨137967716423801921075686745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91978477615867947383791163 137967716423801921075686745)
      ·
        refine ⟨103475787317851440806765059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137967716423801921075686745 103475787317851440806765059)
        ·
          refine ⟨155213680976777161210147589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103475787317851440806765059 155213680976777161210147589)
          ·
            refine ⟨29102565183145717726902673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155213680976777161210147589 29102565183145717726902673)
            ·
              refine ⟨21826923887359288295177005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29102565183145717726902673 21826923887359288295177005)
              ·
                refine ⟨8185096457759733110691377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21826923887359288295177005 8185096457759733110691377)
                ·
                  refine ⟨6138822343319799833018533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8185096457759733110691377 6138822343319799833018533)
                  ·
                    refine ⟨1151029189372462468690975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6138822343319799833018533 1151029189372462468690975)
                    ·
                      rfl

theorem cell22_3362432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3, 2, 4].length) (baseStart_3362432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3362432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3362432 prefixEnd_3362432 := by exact prefixLift 3362432
  have htrace : WordTrace (prefixWord ++ tailWord_3362432) baseStart_3362432 baseEnd_3362432 := by
    simpa [prefixWord, tailWord_3362432, baseEnd_3362432] using wordTrace_append hprefix tailTrace_3362432
  have hstable : (prefixWord ++ tailWord_3362432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362432).length < 2 ^ (prefixWord ++ tailWord_3362432).sum := by decide
  have hdescent : baseEnd_3362432 < baseStart_3362432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362468 : List Nat := [2, 3, 1, 2, 2, 4, 2, 1, 2, 3]
def baseStart_3362468 : Nat := 118140960795 + 3362468 * 2 ^ 59
def prefixEnd_3362468 : Nat := 4983230072969 + 3 ^ 40 * 3362468 * 2
def baseEnd_3362468 : Nat := 1151041512908170374790865

theorem tailTrace_3362468 : CollatzResearch.WordTrace tailWord_3362468 prefixEnd_3362468 1151041512908170374790865 := by
  unfold tailWord_3362468
  simp only [CollatzResearch.WordTrace]
  refine ⟨61319641591180087330016029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81759522121573449773354705 61319641591180087330016029)
  ·
    refine ⟨22994865596692532748756011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61319641591180087330016029 22994865596692532748756011)
    ·
      refine ⟨34492298395038799123134017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22994865596692532748756011 34492298395038799123134017)
      ·
        refine ⟨25869223796279099342350513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34492298395038799123134017 25869223796279099342350513)
        ·
          refine ⟨19401917847209324506762885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25869223796279099342350513 19401917847209324506762885)
          ·
            refine ⟨3637859596351748345018041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19401917847209324506762885 3637859596351748345018041)
            ·
              refine ⟨2728394697263811258763531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3637859596351748345018041 2728394697263811258763531)
              ·
                refine ⟨4092592045895716888145297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2728394697263811258763531 4092592045895716888145297)
                ·
                  refine ⟨3069444034421787666108973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4092592045895716888145297 3069444034421787666108973)
                  ·
                    refine ⟨1151041512908170374790865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3069444034421787666108973 1151041512908170374790865)
                    ·
                      rfl

theorem cell22_3362468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2, 1, 2, 3].length) (baseStart_3362468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3362468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3362468 prefixEnd_3362468 := by exact prefixLift 3362468
  have htrace : WordTrace (prefixWord ++ tailWord_3362468) baseStart_3362468 baseEnd_3362468 := by
    simpa [prefixWord, tailWord_3362468, baseEnd_3362468] using wordTrace_append hprefix tailTrace_3362468
  have hstable : (prefixWord ++ tailWord_3362468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362468).length < 2 ^ (prefixWord ++ tailWord_3362468).sum := by decide
  have hdescent : baseEnd_3362468 < baseStart_3362468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362472 : List Nat := [2, 1, 7, 1, 2, 1, 1, 2, 1, 4]
def baseStart_3362472 : Nat := 118140960795 + 3362472 * 2 ^ 59
def prefixEnd_3362472 : Nat := 4983230072969 + 3 ^ 40 * 3362472 * 2
def baseEnd_3362472 : Nat := 1151042882189915697690853

theorem tailTrace_3362472 : CollatzResearch.WordTrace tailWord_3362472 prefixEnd_3362472 1151042882189915697690853 := by
  unfold tailWord_3362472
  simp only [CollatzResearch.WordTrace]
  refine ⟨61319714537172841671588835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81759619382897122228785113 61319714537172841671588835)
  ·
    refine ⟨91979571805759262507383253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61319714537172841671588835 91979571805759262507383253)
    ·
      refine ⟨2155771214197482715016795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 91979571805759262507383253 2155771214197482715016795)
      ·
        refine ⟨3233656821296224072525193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2155771214197482715016795 3233656821296224072525193)
        ·
          refine ⟨2425242615972168054393895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3233656821296224072525193 2425242615972168054393895)
          ·
            refine ⟨3637863923958252081590843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2425242615972168054393895 3637863923958252081590843)
            ·
              refine ⟨5456795885937378122386265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3637863923958252081590843 5456795885937378122386265)
              ·
                refine ⟨4092596914453033591789699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5456795885937378122386265 4092596914453033591789699)
                ·
                  refine ⟨6138895371679550387684549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4092596914453033591789699 6138895371679550387684549)
                  ·
                    refine ⟨1151042882189915697690853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6138895371679550387684549 1151042882189915697690853)
                    ·
                      rfl

theorem cell22_3362472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_3362472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3362472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3362472 prefixEnd_3362472 := by exact prefixLift 3362472
  have htrace : WordTrace (prefixWord ++ tailWord_3362472) baseStart_3362472 baseEnd_3362472 := by
    simpa [prefixWord, tailWord_3362472, baseEnd_3362472] using wordTrace_append hprefix tailTrace_3362472
  have hstable : (prefixWord ++ tailWord_3362472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362472).length < 2 ^ (prefixWord ++ tailWord_3362472).sum := by decide
  have hdescent : baseEnd_3362472 < baseStart_3362472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362496 : List Nat := [2, 1, 1, 2, 4, 1, 2, 5, 1, 3]
def baseStart_3362496 : Nat := 118140960795 + 3362496 * 2 ^ 59
def prefixEnd_3362496 : Nat := 4983230072969 + 3 ^ 40 * 3362496 * 2
def baseEnd_3362496 : Nat := 1151051097880387635090779

theorem tailTrace_3362496 : CollatzResearch.WordTrace tailWord_3362496 prefixEnd_3362496 1151051097880387635090779 := by
  unfold tailWord_3362496
  simp only [CollatzResearch.WordTrace]
  refine ⟨61320152213129367721025671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81760202950839156961367561 61320152213129367721025671)
  ·
    refine ⟨91980228319694051581538507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61320152213129367721025671 91980228319694051581538507)
    ·
      refine ⟨137970342479541077372307761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91980228319694051581538507 137970342479541077372307761)
      ·
        refine ⟨103477756859655808029230821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137970342479541077372307761 103477756859655808029230821)
        ·
          refine ⟨19402079411185464005480779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103477756859655808029230821 19402079411185464005480779)
          ·
            refine ⟨29103119116778196008221169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19402079411185464005480779 29103119116778196008221169)
            ·
              refine ⟨21827339337583647006165877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29103119116778196008221169 21827339337583647006165877)
              ·
                refine ⟨2046313062898466906828051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21827339337583647006165877 2046313062898466906828051)
                ·
                  refine ⟨3069469594347700360242077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2046313062898466906828051 3069469594347700360242077)
                  ·
                    refine ⟨1151051097880387635090779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3069469594347700360242077 1151051097880387635090779)
                    ·
                      rfl

theorem cell22_3362496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 5, 1, 3].length) (baseStart_3362496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3362496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3362496 prefixEnd_3362496 := by exact prefixLift 3362496
  have htrace : WordTrace (prefixWord ++ tailWord_3362496) baseStart_3362496 baseEnd_3362496 := by
    simpa [prefixWord, tailWord_3362496, baseEnd_3362496] using wordTrace_append hprefix tailTrace_3362496
  have hstable : (prefixWord ++ tailWord_3362496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362496).length < 2 ^ (prefixWord ++ tailWord_3362496).sum := by decide
  have hdescent : baseEnd_3362496 < baseStart_3362496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362498 : List Nat := [3, 5, 1, 2, 2, 9]
def baseStart_3362498 : Nat := 118140960795 + 3362498 * 2 ^ 59
def prefixEnd_3362498 : Nat := 4983230072969 + 3 ^ 40 * 3362498 * 2
def baseEnd_3362498 : Nat := 14210515833595806130133

theorem tailTrace_3362498 : CollatzResearch.WordTrace tailWord_3362498 prefixEnd_3362498 14210515833595806130133 := by
  unfold tailWord_3362498
  simp only [CollatzResearch.WordTrace]
  refine ⟨30660094343062872445906037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81760251581500993189082765 30660094343062872445906037)
  ·
    refine ⟨2874383844662144291803691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30660094343062872445906037 2874383844662144291803691)
    ·
      refine ⟨4311575766993216437705537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2874383844662144291803691 4311575766993216437705537)
      ·
        refine ⟨3233681825244912328279153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4311575766993216437705537 3233681825244912328279153)
        ·
          refine ⟨2425261368933684246209365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3233681825244912328279153 2425261368933684246209365)
          ·
            refine ⟨14210515833595806130133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2425261368933684246209365 14210515833595806130133)
            ·
              rfl

theorem cell22_3362498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 9].length) (baseStart_3362498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3362498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3362498 prefixEnd_3362498 := by exact prefixLift 3362498
  have htrace : WordTrace (prefixWord ++ tailWord_3362498) baseStart_3362498 baseEnd_3362498 := by
    simpa [prefixWord, tailWord_3362498, baseEnd_3362498] using wordTrace_append hprefix tailTrace_3362498
  have hstable : (prefixWord ++ tailWord_3362498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362498).length < 2 ^ (prefixWord ++ tailWord_3362498).sum := by decide
  have hdescent : baseEnd_3362498 < baseStart_3362498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362513 : List Nat := [1, 2, 2, 1, 2, 4, 4, 2, 1, 3]
def baseStart_3362513 : Nat := 118140960795 + 3362513 * 2 ^ 59
def prefixEnd_3362513 : Nat := 4983230072969 + 3 ^ 40 * 3362513 * 2
def baseEnd_3362513 : Nat := 1151056917327805257415727

theorem tailTrace_3362513 : CollatzResearch.WordTrace tailWord_3362513 prefixEnd_3362513 1151056917327805257415727 := by
  unfold tailWord_3362513
  simp only [CollatzResearch.WordTrace]
  refine ⟨122640924467197147345420193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81760616311464764896946795 122640924467197147345420193)
  ·
    refine ⟨91980693350397860509065145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122640924467197147345420193 91980693350397860509065145)
    ·
      refine ⟨68985520012798395381798859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91980693350397860509065145 68985520012798395381798859)
      ·
        refine ⟨103478280019197593072698289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68985520012798395381798859 103478280019197593072698289)
        ·
          refine ⟨77608710014398194804523717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103478280019197593072698289 77608710014398194804523717)
          ·
            refine ⟨14551633127699661525848197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77608710014398194804523717 14551633127699661525848197)
            ·
              refine ⟨2728431211443686536096537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14551633127699661525848197 2728431211443686536096537)
              ·
                refine ⟨2046323408582764902072403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2728431211443686536096537 2046323408582764902072403)
                ·
                  refine ⟨3069485112874147353108605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2046323408582764902072403 3069485112874147353108605)
                  ·
                    refine ⟨1151056917327805257415727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3069485112874147353108605 1151056917327805257415727)
                    ·
                      rfl

theorem cell22_3362513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4, 2, 1, 3].length) (baseStart_3362513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3362513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3362513 prefixEnd_3362513 := by exact prefixLift 3362513
  have htrace : WordTrace (prefixWord ++ tailWord_3362513) baseStart_3362513 baseEnd_3362513 := by
    simpa [prefixWord, tailWord_3362513, baseEnd_3362513] using wordTrace_append hprefix tailTrace_3362513
  have hstable : (prefixWord ++ tailWord_3362513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362513).length < 2 ^ (prefixWord ++ tailWord_3362513).sum := by decide
  have hdescent : baseEnd_3362513 < baseStart_3362513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362552 : List Nat := [2, 1, 2, 1, 1, 2, 2, 3, 3, 5]
def baseStart_3362552 : Nat := 118140960795 + 3362552 * 2 ^ 59
def prefixEnd_3362552 : Nat := 4983230072969 + 3 ^ 40 * 3362552 * 2
def baseEnd_3362552 : Nat := 1151070267824822155690607

theorem tailTrace_3362552 : CollatzResearch.WordTrace tailWord_3362552 prefixEnd_3362552 1151070267824822155690607 := by
  unfold tailWord_3362552
  simp only [CollatzResearch.WordTrace]
  refine ⟨61321173457027928503044955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81761564609370571337393273 61321173457027928503044955)
  ·
    refine ⟨91981760185541892754567433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61321173457027928503044955 91981760185541892754567433)
    ·
      refine ⟨68986320139156419565925575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91981760185541892754567433 68986320139156419565925575)
      ·
        refine ⟨103479480208734629348888363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68986320139156419565925575 103479480208734629348888363)
        ·
          refine ⟨155219220313101944023332545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103479480208734629348888363 155219220313101944023332545)
          ·
            refine ⟨116414415234826458017499409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155219220313101944023332545 116414415234826458017499409)
            ·
              refine ⟨87310811426119843513124557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116414415234826458017499409 87310811426119843513124557)
              ·
                refine ⟨32741554284794941317421709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87310811426119843513124557 32741554284794941317421709)
                ·
                  refine ⟨12278082856798102994033141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32741554284794941317421709 12278082856798102994033141)
                  ·
                    refine ⟨1151070267824822155690607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12278082856798102994033141 1151070267824822155690607)
                    ·
                      rfl

theorem cell22_3362552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 3, 5].length) (baseStart_3362552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3362552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3362552 prefixEnd_3362552 := by exact prefixLift 3362552
  have htrace : WordTrace (prefixWord ++ tailWord_3362552) baseStart_3362552 baseEnd_3362552 := by
    simpa [prefixWord, tailWord_3362552, baseEnd_3362552] using wordTrace_append hprefix tailTrace_3362552
  have hstable : (prefixWord ++ tailWord_3362552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362552).length < 2 ^ (prefixWord ++ tailWord_3362552).sum := by decide
  have hdescent : baseEnd_3362552 < baseStart_3362552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362586 : List Nat := [3, 1, 1, 3, 2, 4, 1, 1, 1, 5]
def baseStart_3362586 : Nat := 118140960795 + 3362586 * 2 ^ 59
def prefixEnd_3362586 : Nat := 4983230072969 + 3 ^ 40 * 3362586 * 2
def baseEnd_3362586 : Nat := 1151081906719657400340503

theorem tailTrace_3362586 : CollatzResearch.WordTrace tailWord_3362586 prefixEnd_3362586 1151081906719657400340503 := by
  unfold tailWord_3362586
  simp only [CollatzResearch.WordTrace]
  refine ⟨30660896748983170203206903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81762391330621787208551741 30660896748983170203206903)
  ·
    refine ⟨45991345123474755304810355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30660896748983170203206903 45991345123474755304810355)
    ·
      refine ⟨68987017685212132957215533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45991345123474755304810355 68987017685212132957215533)
      ·
        refine ⟨25870131631954549858955825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68987017685212132957215533 25870131631954549858955825)
        ·
          refine ⟨19402598723965912394216869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25870131631954549858955825 19402598723965912394216869)
          ·
            refine ⟨3637987260743608573915663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19402598723965912394216869 3637987260743608573915663)
            ·
              refine ⟨5456980891115412860873495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3637987260743608573915663 5456980891115412860873495)
              ·
                refine ⟨8185471336673119291310243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5456980891115412860873495 8185471336673119291310243)
                ·
                  refine ⟨12278207005009678936965365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8185471336673119291310243 12278207005009678936965365)
                  ·
                    refine ⟨1151081906719657400340503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12278207005009678936965365 1151081906719657400340503)
                    ·
                      rfl

theorem cell22_3362586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 1, 1, 5].length) (baseStart_3362586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3362586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3362586 prefixEnd_3362586 := by exact prefixLift 3362586
  have htrace : WordTrace (prefixWord ++ tailWord_3362586) baseStart_3362586 baseEnd_3362586 := by
    simpa [prefixWord, tailWord_3362586, baseEnd_3362586] using wordTrace_append hprefix tailTrace_3362586
  have hstable : (prefixWord ++ tailWord_3362586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362586).length < 2 ^ (prefixWord ++ tailWord_3362586).sum := by decide
  have hdescent : baseEnd_3362586 < baseStart_3362586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362631 : List Nat := [1, 1, 4, 1, 2, 1, 5, 1, 3, 3]
def baseStart_3362631 : Nat := 118140960795 + 3362631 * 2 ^ 59
def prefixEnd_3362631 : Nat := 4983230072969 + 3 ^ 40 * 3362631 * 2
def baseEnd_3362631 : Nat := 1151097311139292282965365

theorem tailTrace_3362631 : CollatzResearch.WordTrace tailWord_3362631 prefixEnd_3362631 1151097311139292282965365 := by
  unfold tailWord_3362631
  simp only [CollatzResearch.WordTrace]
  refine ⟨122645228280769653498215747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81763485520513102332143831 122645228280769653498215747)
  ·
    refine ⟨183967842421154480247323621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122645228280769653498215747 183967842421154480247323621)
    ·
      refine ⟨34493970453966465046373179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 183967842421154480247323621 34493970453966465046373179)
      ·
        refine ⟨51740955680949697569559769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34493970453966465046373179 51740955680949697569559769)
        ·
          refine ⟨38805716760712273177169827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51740955680949697569559769 38805716760712273177169827)
          ·
            refine ⟨58208575141068409765754741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38805716760712273177169827 58208575141068409765754741)
            ·
              refine ⟨5457053919475163415539507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58208575141068409765754741 5457053919475163415539507)
              ·
                refine ⟨8185580879212745123309261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5457053919475163415539507 8185580879212745123309261)
                ·
                  refine ⟨3069592829704779421240973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8185580879212745123309261 3069592829704779421240973)
                  ·
                    refine ⟨1151097311139292282965365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3069592829704779421240973 1151097311139292282965365)
                    ·
                      rfl

theorem cell22_3362631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 1, 3, 3].length) (baseStart_3362631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3362631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3362631 prefixEnd_3362631 := by exact prefixLift 3362631
  have htrace : WordTrace (prefixWord ++ tailWord_3362631) baseStart_3362631 baseEnd_3362631 := by
    simpa [prefixWord, tailWord_3362631, baseEnd_3362631] using wordTrace_append hprefix tailTrace_3362631
  have hstable : (prefixWord ++ tailWord_3362631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362631).length < 2 ^ (prefixWord ++ tailWord_3362631).sum := by decide
  have hdescent : baseEnd_3362631 < baseStart_3362631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362637 : List Nat := [1, 6, 1, 2, 1, 3, 2, 1, 2, 3]
def baseStart_3362637 : Nat := 118140960795 + 3362637 * 2 ^ 59
def prefixEnd_3362637 : Nat := 4983230072969 + 3 ^ 40 * 3362637 * 2
def baseEnd_3362637 : Nat := 1151099365061910267315347

theorem tailTrace_3362637 : CollatzResearch.WordTrace tailWord_3362637 prefixEnd_3362637 1151099365061910267315347 := by
  unfold tailWord_3362637
  simp only [CollatzResearch.WordTrace]
  refine ⟨122645447118747916522934165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81763631412498611015289443 122645447118747916522934165)
  ·
    refine ⟨5749005333691308587012539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 122645447118747916522934165 5749005333691308587012539)
    ·
      refine ⟨8623508000536962880518809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5749005333691308587012539 8623508000536962880518809)
      ·
        refine ⟨6467631000402722160389107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8623508000536962880518809 6467631000402722160389107)
        ·
          refine ⟨9701446500604083240583661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6467631000402722160389107 9701446500604083240583661)
          ·
            refine ⟨3638042437726531215218873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9701446500604083240583661 3638042437726531215218873)
            ·
              refine ⟨2728531828294898411414155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3638042437726531215218873 2728531828294898411414155)
              ·
                refine ⟨4092797742442347617121233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2728531828294898411414155 4092797742442347617121233)
                ·
                  refine ⟨3069598306831760712840925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4092797742442347617121233 3069598306831760712840925)
                  ·
                    refine ⟨1151099365061910267315347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3069598306831760712840925 1151099365061910267315347)
                    ·
                      rfl

theorem cell22_3362637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_3362637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3362637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3362637 prefixEnd_3362637 := by exact prefixLift 3362637
  have htrace : WordTrace (prefixWord ++ tailWord_3362637) baseStart_3362637 baseEnd_3362637 := by
    simpa [prefixWord, tailWord_3362637, baseEnd_3362637] using wordTrace_append hprefix tailTrace_3362637
  have hstable : (prefixWord ++ tailWord_3362637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362637).length < 2 ^ (prefixWord ++ tailWord_3362637).sum := by decide
  have hdescent : baseEnd_3362637 < baseStart_3362637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362704 : List Nat := [2, 1, 1, 1, 1, 1, 2, 7, 1, 5]
def baseStart_3362704 : Nat := 118140960795 + 3362704 * 2 ^ 59
def prefixEnd_3362704 : Nat := 4983230072969 + 3 ^ 40 * 3362704 * 2
def baseEnd_3362704 : Nat := 1151122300531144425890141

theorem tailTrace_3362704 : CollatzResearch.WordTrace tailWord_3362704 prefixEnd_3362704 1151122300531144425890141 := by
  unfold tailWord_3362704
  simp only [CollatzResearch.WordTrace]
  refine ⟨61323945404752593482811583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81765260539670124643748777 61323945404752593482811583)
  ·
    refine ⟨91985918107128890224217375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61323945404752593482811583 91985918107128890224217375)
    ·
      refine ⟨137978877160693335336326063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91985918107128890224217375 137978877160693335336326063)
      ·
        refine ⟨206968315741040003004489095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137978877160693335336326063 206968315741040003004489095)
        ·
          refine ⟨310452473611560004506733643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206968315741040003004489095 310452473611560004506733643)
          ·
            refine ⟨465678710417340006760100465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310452473611560004506733643 465678710417340006760100465)
            ·
              refine ⟨349259032813005005070075349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 465678710417340006760100465 349259032813005005070075349)
              ·
                refine ⟨8185758581554804806329891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 349259032813005005070075349 8185758581554804806329891)
                ·
                  refine ⟨12278637872332207209494837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8185758581554804806329891 12278637872332207209494837)
                  ·
                    refine ⟨1151122300531144425890141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12278637872332207209494837 1151122300531144425890141)
                    ·
                      rfl

theorem cell22_3362704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7, 1, 5].length) (baseStart_3362704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3362704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3362704 prefixEnd_3362704 := by exact prefixLift 3362704
  have htrace : WordTrace (prefixWord ++ tailWord_3362704) baseStart_3362704 baseEnd_3362704 := by
    simpa [prefixWord, tailWord_3362704, baseEnd_3362704] using wordTrace_append hprefix tailTrace_3362704
  have hstable : (prefixWord ++ tailWord_3362704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362704).length < 2 ^ (prefixWord ++ tailWord_3362704).sum := by decide
  have hdescent : baseEnd_3362704 < baseStart_3362704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362706 : List Nat := [3, 2, 3, 2, 1, 1, 1, 1, 8]
def baseStart_3362706 : Nat := 118140960795 + 3362706 * 2 ^ 59
def prefixEnd_3362706 : Nat := 4983230072969 + 3 ^ 40 * 3362706 * 2
def baseEnd_3362706 : Nat := 383707661724005695780045

theorem tailTrace_3362706 : CollatzResearch.WordTrace tailWord_3362706 prefixEnd_3362706 383707661724005695780045 := by
  unfold tailWord_3362706
  simp only [CollatzResearch.WordTrace]
  refine ⟨30661990938874485326798993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81765309170331960871463981 30661990938874485326798993)
  ·
    refine ⟨22996493204155863995099245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30661990938874485326798993 22996493204155863995099245)
    ·
      refine ⟨8623684951558448998162217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22996493204155863995099245 8623684951558448998162217)
      ·
        refine ⟨6467763713668836748621663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8623684951558448998162217 6467763713668836748621663)
        ·
          refine ⟨9701645570503255122932495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6467763713668836748621663 9701645570503255122932495)
          ·
            refine ⟨14552468355754882684398743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9701645570503255122932495 14552468355754882684398743)
            ·
              refine ⟨21828702533632324026598115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14552468355754882684398743 21828702533632324026598115)
              ·
                refine ⟨32743053800448486039897173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21828702533632324026598115 32743053800448486039897173)
                ·
                  refine ⟨383707661724005695780045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32743053800448486039897173 383707661724005695780045)
                  ·
                    rfl

theorem cell22_3362706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 8].length) (baseStart_3362706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3362706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3362706 prefixEnd_3362706 := by exact prefixLift 3362706
  have htrace : WordTrace (prefixWord ++ tailWord_3362706) baseStart_3362706 baseEnd_3362706 := by
    simpa [prefixWord, tailWord_3362706, baseEnd_3362706] using wordTrace_append hprefix tailTrace_3362706
  have hstable : (prefixWord ++ tailWord_3362706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362706).length < 2 ^ (prefixWord ++ tailWord_3362706).sum := by decide
  have hdescent : baseEnd_3362706 < baseStart_3362706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362740 : List Nat := [2, 5, 2, 1, 2, 1, 2, 1, 6]
def baseStart_3362740 : Nat := 118140960795 + 3362740 * 2 ^ 59
def prefixEnd_3362740 : Nat := 4983230072969 + 3 ^ 40 * 3362740 * 2
def baseEnd_3362740 : Nat := 383711541355617443996677

theorem tailTrace_3362740 : CollatzResearch.WordTrace tailWord_3362740 prefixEnd_3362740 383711541355617443996677 := by
  unfold tailWord_3362740
  simp only [CollatzResearch.WordTrace]
  refine ⟨61324601918687382556966837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81766135891583176742622449 61324601918687382556966837)
  ·
    refine ⟨5749181429876942114715641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61324601918687382556966837 5749181429876942114715641)
    ·
      refine ⟨4311886072407706586036731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5749181429876942114715641 4311886072407706586036731)
      ·
        refine ⟨6467829108611559879055097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4311886072407706586036731 6467829108611559879055097)
        ·
          refine ⟨4850871831458669909291323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6467829108611559879055097 4850871831458669909291323)
          ·
            refine ⟨7276307747188004863936985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4850871831458669909291323 7276307747188004863936985)
            ·
              refine ⟨5457230810391003647952739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7276307747188004863936985 5457230810391003647952739)
              ·
                refine ⟨8185846215586505471929109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5457230810391003647952739 8185846215586505471929109)
                ·
                  refine ⟨383711541355617443996677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8185846215586505471929109 383711541355617443996677)
                  ·
                    rfl

theorem cell22_3362740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_3362740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3362740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3362740 prefixEnd_3362740 := by exact prefixLift 3362740
  have htrace : WordTrace (prefixWord ++ tailWord_3362740) baseStart_3362740 baseEnd_3362740 := by
    simpa [prefixWord, tailWord_3362740, baseEnd_3362740] using wordTrace_append hprefix tailTrace_3362740
  have hstable : (prefixWord ++ tailWord_3362740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362740).length < 2 ^ (prefixWord ++ tailWord_3362740).sum := by decide
  have hdescent : baseEnd_3362740 < baseStart_3362740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362774 : List Nat := [5, 2, 1, 1, 4, 1, 1, 3, 4]
def baseStart_3362774 : Nat := 118140960795 + 3362774 * 2 ^ 59
def prefixEnd_3362774 : Nat := 4983230072969 + 3 ^ 40 * 3362774 * 2
def baseEnd_3362774 : Nat := 383715420987229192213309

theorem tailTrace_3362774 : CollatzResearch.WordTrace tailWord_3362774 prefixEnd_3362774 383715420987229192213309 := by
  unfold tailWord_3362774
  simp only [CollatzResearch.WordTrace]
  refine ⟨7665652744953224307541961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81766962612834392613780917 7665652744953224307541961)
  ·
    refine ⟨5749239558714918230656471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7665652744953224307541961 5749239558714918230656471)
    ·
      refine ⟨8623859338072377345984707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5749239558714918230656471 8623859338072377345984707)
      ·
        refine ⟨12935789007108566018977061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8623859338072377345984707 12935789007108566018977061)
        ·
          refine ⟨2425460438832856128558199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12935789007108566018977061 2425460438832856128558199)
          ·
            refine ⟨3638190658249284192837299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2425460438832856128558199 3638190658249284192837299)
            ·
              refine ⟨5457285987373926289255949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3638190658249284192837299 5457285987373926289255949)
              ·
                refine ⟨2046482245265222358470981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5457285987373926289255949 2046482245265222358470981)
                ·
                  refine ⟨383715420987229192213309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2046482245265222358470981 383715420987229192213309)
                  ·
                    rfl

theorem cell22_3362774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_3362774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3362774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3362774 prefixEnd_3362774 := by exact prefixLift 3362774
  have htrace : WordTrace (prefixWord ++ tailWord_3362774) baseStart_3362774 baseEnd_3362774 := by
    simpa [prefixWord, tailWord_3362774, baseEnd_3362774] using wordTrace_append hprefix tailTrace_3362774
  have hstable : (prefixWord ++ tailWord_3362774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362774).length < 2 ^ (prefixWord ++ tailWord_3362774).sum := by decide
  have hdescent : baseEnd_3362774 < baseStart_3362774 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362813 : List Nat := [1, 4, 1, 1, 1, 2, 6, 1, 5]
def baseStart_3362813 : Nat := 118140960795 + 3362813 * 2 ^ 59
def prefixEnd_3362813 : Nat := 4983230072969 + 3 ^ 40 * 3362813 * 2
def baseEnd_3362813 : Nat := 383719871152901491638269

theorem tailTrace_3362813 : CollatzResearch.WordTrace tailWord_3362813 prefixEnd_3362813 383719871152901491638269 := by
  unfold tailWord_3362813
  simp only [CollatzResearch.WordTrace]
  refine ⟨122651866366110298581341093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81767910910740199054227395 122651866366110298581341093)
  ·
    refine ⟨22997224943645680984001455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122651866366110298581341093 22997224943645680984001455)
    ·
      refine ⟨34495837415468521476002183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22997224943645680984001455 34495837415468521476002183)
      ·
        refine ⟨51743756123202782214003275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34495837415468521476002183 51743756123202782214003275)
        ·
          refine ⟨77615634184804173321004913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51743756123202782214003275 77615634184804173321004913)
          ·
            refine ⟨58211725638603129990753685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77615634184804173321004913 58211725638603129990753685)
            ·
              refine ⟨2728674639309521718316579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 58211725638603129990753685 2728674639309521718316579)
              ·
                refine ⟨4093011958964282577474869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2728674639309521718316579 4093011958964282577474869)
                ·
                  refine ⟨383719871152901491638269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4093011958964282577474869 383719871152901491638269)
                  ·
                    rfl

theorem cell22_3362813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6, 1, 5].length) (baseStart_3362813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3362813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3362813 prefixEnd_3362813 := by exact prefixLift 3362813
  have htrace : WordTrace (prefixWord ++ tailWord_3362813) baseStart_3362813 baseEnd_3362813 := by
    simpa [prefixWord, tailWord_3362813, baseEnd_3362813] using wordTrace_append hprefix tailTrace_3362813
  have hstable : (prefixWord ++ tailWord_3362813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362813).length < 2 ^ (prefixWord ++ tailWord_3362813).sum := by decide
  have hdescent : baseEnd_3362813 < baseStart_3362813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362871 : List Nat := [1, 1, 3, 1, 2, 2, 2, 2, 4, 4]
def baseStart_3362871 : Nat := 118140960795 + 3362871 * 2 ^ 59
def prefixEnd_3362871 : Nat := 4983230072969 + 3 ^ 40 * 3362871 * 2
def baseEnd_3362871 : Nat := 1151179468044011656964629

theorem tailTrace_3362871 : CollatzResearch.WordTrace tailWord_3362871 prefixEnd_3362871 1151179468044011656964629 := by
  unfold tailWord_3362871
  simp only [CollatzResearch.WordTrace]
  refine ⟨122653981799900174486952467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81769321199933449657968311 122653981799900174486952467)
  ·
    refine ⟨183980972699850261730428701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122653981799900174486952467 183980972699850261730428701)
    ·
      refine ⟨68992864762443848148910763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183980972699850261730428701 68992864762443848148910763)
      ·
        refine ⟨103489297143665772223366145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68992864762443848148910763 103489297143665772223366145)
        ·
          refine ⟨77616972857749329167524609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103489297143665772223366145 77616972857749329167524609)
          ·
            refine ⟨58212729643311996875643457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77616972857749329167524609 58212729643311996875643457)
            ·
              refine ⟨43659547232483997656732593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58212729643311996875643457 43659547232483997656732593)
              ·
                refine ⟨32744660424362998242549445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43659547232483997656732593 32744660424362998242549445)
                ·
                  refine ⟨6139623829568062170478021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32744660424362998242549445 6139623829568062170478021)
                  ·
                    refine ⟨1151179468044011656964629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6139623829568062170478021 1151179468044011656964629)
                    ·
                      rfl

theorem cell22_3362871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 4, 4].length) (baseStart_3362871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3362871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3362871 prefixEnd_3362871 := by exact prefixLift 3362871
  have htrace : WordTrace (prefixWord ++ tailWord_3362871) baseStart_3362871 baseEnd_3362871 := by
    simpa [prefixWord, tailWord_3362871, baseEnd_3362871] using wordTrace_append hprefix tailTrace_3362871
  have hstable : (prefixWord ++ tailWord_3362871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362871).length < 2 ^ (prefixWord ++ tailWord_3362871).sum := by decide
  have hdescent : baseEnd_3362871 < baseStart_3362871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362916 : List Nat := [2, 3, 1, 1, 2, 1, 2, 1, 1, 8]
def baseStart_3362916 : Nat := 118140960795 + 3362916 * 2 ^ 59
def prefixEnd_3362916 : Nat := 4983230072969 + 3 ^ 40 * 3362916 * 2
def baseEnd_3362916 : Nat := 1151194872463646539589491

theorem tailTrace_3362916 : CollatzResearch.WordTrace tailWord_3362916 prefixEnd_3362916 1151194872463646539589491 := by
  unfold tailWord_3362916
  simp only [CollatzResearch.WordTrace]
  refine ⟨61327811542368573586170301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81770415389824764781560401 61327811542368573586170301)
  ·
    refine ⟨22997929328388215094813863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61327811542368573586170301 22997929328388215094813863)
    ·
      refine ⟨34496893992582322642220795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22997929328388215094813863 34496893992582322642220795)
      ·
        refine ⟨51745340988873483963331193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34496893992582322642220795 51745340988873483963331193)
        ·
          refine ⟨38809005741655112972498395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51745340988873483963331193 38809005741655112972498395)
          ·
            refine ⟨58213508612482669458747593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38809005741655112972498395 58213508612482669458747593)
            ·
              refine ⟨43660131459362002094060695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58213508612482669458747593 43660131459362002094060695)
              ·
                refine ⟨65490197189043003141091043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43660131459362002094060695 65490197189043003141091043)
                ·
                  refine ⟨98235295783564504711636565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65490197189043003141091043 98235295783564504711636565)
                  ·
                    refine ⟨1151194872463646539589491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 98235295783564504711636565 1151194872463646539589491)
                    ·
                      rfl

theorem cell22_3362916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_3362916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3362916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3362916 prefixEnd_3362916 := by exact prefixLift 3362916
  have htrace : WordTrace (prefixWord ++ tailWord_3362916) baseStart_3362916 baseEnd_3362916 := by
    simpa [prefixWord, tailWord_3362916, baseEnd_3362916] using wordTrace_append hprefix tailTrace_3362916
  have hstable : (prefixWord ++ tailWord_3362916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362916).length < 2 ^ (prefixWord ++ tailWord_3362916).sum := by decide
  have hdescent : baseEnd_3362916 < baseStart_3362916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363008 : List Nat := [2, 1, 1, 2, 5, 1, 1, 1, 3, 5]
def baseStart_3363008 : Nat := 118140960795 + 3363008 * 2 ^ 59
def prefixEnd_3363008 : Nat := 4983230072969 + 3 ^ 40 * 3363008 * 2
def baseEnd_3363008 : Nat := 1151226365943788966289209

theorem tailTrace_3363008 : CollatzResearch.WordTrace tailWord_3363008 prefixEnd_3363008 1151226365943788966289209 := by
  unfold tailWord_3363008
  simp only [CollatzResearch.WordTrace]
  refine ⟨61329489300201923442344839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81772652400269231256459785 61329489300201923442344839)
  ·
    refine ⟨91994233950302885163517259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61329489300201923442344839 91994233950302885163517259)
    ·
      refine ⟨137991350925454327745275889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91994233950302885163517259 137991350925454327745275889)
      ·
        refine ⟨103493513194090745808956917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137991350925454327745275889 103493513194090745808956917)
        ·
          refine ⟨9702516861946007419589711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 103493513194090745808956917 9702516861946007419589711)
          ·
            refine ⟨14553775292919011129384567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9702516861946007419589711 14553775292919011129384567)
            ·
              refine ⟨21830662939378516694076851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14553775292919011129384567 21830662939378516694076851)
              ·
                refine ⟨32745994409067775041115277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21830662939378516694076851 32745994409067775041115277)
                ·
                  refine ⟨12279747903400415640418229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32745994409067775041115277 12279747903400415640418229)
                  ·
                    refine ⟨1151226365943788966289209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12279747903400415640418229 1151226365943788966289209)
                    ·
                      rfl

theorem cell22_3363008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 3, 5].length) (baseStart_3363008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3363008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3363008 prefixEnd_3363008 := by exact prefixLift 3363008
  have htrace : WordTrace (prefixWord ++ tailWord_3363008) baseStart_3363008 baseEnd_3363008 := by
    simpa [prefixWord, tailWord_3363008, baseEnd_3363008] using wordTrace_append hprefix tailTrace_3363008
  have hstable : (prefixWord ++ tailWord_3363008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363008).length < 2 ^ (prefixWord ++ tailWord_3363008).sum := by decide
  have hdescent : baseEnd_3363008 < baseStart_3363008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363023 : List Nat := [1, 1, 2, 1, 1, 3, 3, 4, 2, 4]
def baseStart_3363023 : Nat := 118140960795 + 3363023 * 2 ^ 59
def prefixEnd_3363023 : Nat := 4983230072969 + 3 ^ 40 * 3363023 * 2
def baseEnd_3363023 : Nat := 1151231500750333927164163

theorem tailTrace_3363023 : CollatzResearch.WordTrace tailWord_3363023 prefixEnd_3363023 1151231500750333927164163 := by
  unfold tailWord_3363023
  simp only [CollatzResearch.WordTrace]
  refine ⟨122659525695349504446485723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81773017130233002964323815 122659525695349504446485723)
  ·
    refine ⟨183989288543024256669728585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122659525695349504446485723 183989288543024256669728585)
    ·
      refine ⟨137991966407268192502296439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183989288543024256669728585 137991966407268192502296439)
      ·
        refine ⟨206987949610902288753444659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137991966407268192502296439 206987949610902288753444659)
        ·
          refine ⟨310481924416353433130166989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206987949610902288753444659 310481924416353433130166989)
          ·
            refine ⟨116430721656132537423812621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 310481924416353433130166989 116430721656132537423812621)
            ·
              refine ⟨43661520621049701533929733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116430721656132537423812621 43661520621049701533929733)
              ·
                refine ⟨8186535116446819037611825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43661520621049701533929733 8186535116446819037611825)
                ·
                  refine ⟨6139901337335114278208869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8186535116446819037611825 6139901337335114278208869)
                  ·
                    refine ⟨1151231500750333927164163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6139901337335114278208869 1151231500750333927164163)
                    ·
                      rfl

theorem cell22_3363023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4, 2, 4].length) (baseStart_3363023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3363023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3363023 prefixEnd_3363023 := by exact prefixLift 3363023
  have htrace : WordTrace (prefixWord ++ tailWord_3363023) baseStart_3363023 baseEnd_3363023 := by
    simpa [prefixWord, tailWord_3363023, baseEnd_3363023] using wordTrace_append hprefix tailTrace_3363023
  have hstable : (prefixWord ++ tailWord_3363023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363023).length < 2 ^ (prefixWord ++ tailWord_3363023).sum := by decide
  have hdescent : baseEnd_3363023 < baseStart_3363023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363025 : List Nat := [1, 2, 2, 1, 2, 2, 3, 4, 2, 3]
def baseStart_3363025 : Nat := 118140960795 + 3363025 * 2 ^ 59
def prefixEnd_3363025 : Nat := 4983230072969 + 3 ^ 40 * 3363025 * 2
def baseEnd_3363025 : Nat := 1151232185391206588614157

theorem tailTrace_3363025 : CollatzResearch.WordTrace tailWord_3363025 prefixEnd_3363025 1151232185391206588614157 := by
  unfold tailWord_3363025
  simp only [CollatzResearch.WordTrace]
  refine ⟨122659598641342258788058529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81773065760894839192039019 122659598641342258788058529)
  ·
    refine ⟨91994698981006694091043897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122659598641342258788058529 91994698981006694091043897)
    ·
      refine ⟨68996024235755020568282923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91994698981006694091043897 68996024235755020568282923)
      ·
        refine ⟨103494036353632530852424385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68996024235755020568282923 103494036353632530852424385)
        ·
          refine ⟨77620527265224398139318289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103494036353632530852424385 77620527265224398139318289)
          ·
            refine ⟨58215395448918298604488717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77620527265224398139318289 58215395448918298604488717)
            ·
              refine ⟨21830773293344361976683269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58215395448918298604488717 21830773293344361976683269)
              ·
                refine ⟨4093269992502067870628113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21830773293344361976683269 4093269992502067870628113)
                ·
                  refine ⟨3069952494376550902971085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4093269992502067870628113 3069952494376550902971085)
                  ·
                    refine ⟨1151232185391206588614157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3069952494376550902971085 1151232185391206588614157)
                    ·
                      rfl

theorem cell22_3363025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 4, 2, 3].length) (baseStart_3363025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3363025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3363025 prefixEnd_3363025 := by exact prefixLift 3363025
  have htrace : WordTrace (prefixWord ++ tailWord_3363025) baseStart_3363025 baseEnd_3363025 := by
    simpa [prefixWord, tailWord_3363025, baseEnd_3363025] using wordTrace_append hprefix tailTrace_3363025
  have hstable : (prefixWord ++ tailWord_3363025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363025).length < 2 ^ (prefixWord ++ tailWord_3363025).sum := by decide
  have hdescent : baseEnd_3363025 < baseStart_3363025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363055 : List Nat := [1, 1, 2, 1, 6, 2, 3, 6]
def baseStart_3363055 : Nat := 118140960795 + 3363055 * 2 ^ 59
def prefixEnd_3363055 : Nat := 4983230072969 + 3 ^ 40 * 3363055 * 2
def baseEnd_3363055 : Nat := 127915828333810723373785

theorem tailTrace_3363055 : CollatzResearch.WordTrace tailWord_3363055 prefixEnd_3363055 127915828333810723373785 := by
  unfold tailWord_3363055
  simp only [CollatzResearch.WordTrace]
  refine ⟨122660692831233573911650619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81773795220822382607767079 122660692831233573911650619)
  ·
    refine ⟨183991039246850360867475929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122660692831233573911650619 183991039246850360867475929)
    ·
      refine ⟨137993279435137770650606947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183991039246850360867475929 137993279435137770650606947)
      ·
        refine ⟨206989919152706655975910421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137993279435137770650606947 206989919152706655975910421)
        ·
          refine ⟨9702652460283124498870801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 206989919152706655975910421 9702652460283124498870801)
          ·
            refine ⟨7276989345212343374153101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9702652460283124498870801 7276989345212343374153101)
            ·
              refine ⟨2728871004454628765307413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7276989345212343374153101 2728871004454628765307413)
              ·
                refine ⟨127915828333810723373785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2728871004454628765307413 127915828333810723373785)
                ·
                  rfl

theorem cell22_3363055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3, 6].length) (baseStart_3363055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3363055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3363055 prefixEnd_3363055 := by exact prefixLift 3363055
  have htrace : WordTrace (prefixWord ++ tailWord_3363055) baseStart_3363055 baseEnd_3363055 := by
    simpa [prefixWord, tailWord_3363055, baseEnd_3363055] using wordTrace_append hprefix tailTrace_3363055
  have hstable : (prefixWord ++ tailWord_3363055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363055).length < 2 ^ (prefixWord ++ tailWord_3363055).sum := by decide
  have hdescent : baseEnd_3363055 < baseStart_3363055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363076 : List Nat := [2, 3, 2, 2, 4, 1, 1, 2, 2, 3]
def baseStart_3363076 : Nat := 118140960795 + 3363076 * 2 ^ 59
def prefixEnd_3363076 : Nat := 4983230072969 + 3 ^ 40 * 3363076 * 2
def baseEnd_3363076 : Nat := 1151249643733459455589001

theorem tailTrace_3363076 : CollatzResearch.WordTrace tailWord_3363076 prefixEnd_3363076 1151249643733459455589001 := by
  unfold tailWord_3363076
  simp only [CollatzResearch.WordTrace]
  refine ⟨61330729382078747249082541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81774305842771662998776721 61330729382078747249082541)
  ·
    refine ⟨22999023518279530218405953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61330729382078747249082541 22999023518279530218405953)
    ·
      refine ⟨17249267638709647663804465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22999023518279530218405953 17249267638709647663804465)
      ·
        refine ⟨12936950729032235747853349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17249267638709647663804465 12936950729032235747853349)
        ·
          refine ⟨2425678261693544202722503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12936950729032235747853349 2425678261693544202722503)
          ·
            refine ⟨3638517392540316304083755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2425678261693544202722503 3638517392540316304083755)
            ·
              refine ⟨5457776088810474456125633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3638517392540316304083755 5457776088810474456125633)
              ·
                refine ⟨4093332066607855842094225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5457776088810474456125633 4093332066607855842094225)
                ·
                  refine ⟨3069999049955891881570669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4093332066607855842094225 3069999049955891881570669)
                  ·
                    refine ⟨1151249643733459455589001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3069999049955891881570669 1151249643733459455589001)
                    ·
                      rfl

theorem cell22_3363076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 2, 2, 3].length) (baseStart_3363076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3363076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3363076 prefixEnd_3363076 := by exact prefixLift 3363076
  have htrace : WordTrace (prefixWord ++ tailWord_3363076) baseStart_3363076 baseEnd_3363076 := by
    simpa [prefixWord, tailWord_3363076, baseEnd_3363076] using wordTrace_append hprefix tailTrace_3363076
  have hstable : (prefixWord ++ tailWord_3363076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363076).length < 2 ^ (prefixWord ++ tailWord_3363076).sum := by decide
  have hdescent : baseEnd_3363076 < baseStart_3363076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363083 : List Nat := [1, 1, 1, 1, 5, 2, 3, 1, 7]
def baseStart_3363083 : Nat := 118140960795 + 3363083 * 2 ^ 59
def prefixEnd_3363083 : Nat := 4983230072969 + 3 ^ 40 * 3363083 * 2
def baseEnd_3363083 : Nat := 383750679992171256887993

theorem tailTrace_3363083 : CollatzResearch.WordTrace tailWord_3363083 prefixEnd_3363083 383750679992171256887993 := by
  unfold tailWord_3363083
  simp only [CollatzResearch.WordTrace]
  refine ⟨122661714075132134693669903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81774476050088089795779935 122661714075132134693669903)
  ·
    refine ⟨183992571112698202040504855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122661714075132134693669903 183992571112698202040504855)
    ·
      refine ⟨275988856669047303060757283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183992571112698202040504855 275988856669047303060757283)
      ·
        refine ⟨413983285003570954591135925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275988856669047303060757283 413983285003570954591135925)
        ·
          refine ⟨38810932969084776992918993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 413983285003570954591135925 38810932969084776992918993)
          ·
            refine ⟨29108199726813582744689245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38810932969084776992918993 29108199726813582744689245)
            ·
              refine ⟨10915574897555093529258467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29108199726813582744689245 10915574897555093529258467)
              ·
                refine ⟨16373362346332640293887701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10915574897555093529258467 16373362346332640293887701)
                ·
                  refine ⟨383750679992171256887993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16373362346332640293887701 383750679992171256887993)
                  ·
                    rfl

theorem cell22_3363083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 7].length) (baseStart_3363083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3363083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3363083 prefixEnd_3363083 := by exact prefixLift 3363083
  have htrace : WordTrace (prefixWord ++ tailWord_3363083) baseStart_3363083 baseEnd_3363083 := by
    simpa [prefixWord, tailWord_3363083, baseEnd_3363083] using wordTrace_append hprefix tailTrace_3363083
  have hstable : (prefixWord ++ tailWord_3363083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363083).length < 2 ^ (prefixWord ++ tailWord_3363083).sum := by decide
  have hdescent : baseEnd_3363083 < baseStart_3363083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363121 : List Nat := [1, 2, 2, 3, 4, 2, 1, 3, 1, 3]
def baseStart_3363121 : Nat := 118140960795 + 3363121 * 2 ^ 59
def prefixEnd_3363121 : Nat := 4983230072969 + 3 ^ 40 * 3363121 * 2
def baseEnd_3363121 : Nat := 1151265048153094338213863

theorem tailTrace_3363121 : CollatzResearch.WordTrace tailWord_3363121 prefixEnd_3363121 1151265048153094338213863 := by
  unfold tailWord_3363121
  simp only [CollatzResearch.WordTrace]
  refine ⟨122663100048994467183553217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81775400032662978122368811 122663100048994467183553217)
  ·
    refine ⟨91997325036745850387664913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122663100048994467183553217 91997325036745850387664913)
    ·
      refine ⟨68997993777559387790748685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91997325036745850387664913 68997993777559387790748685)
      ·
        refine ⟨25874247666584770421530757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68997993777559387790748685 25874247666584770421530757)
        ·
          refine ⟨4851421437484644454037017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25874247666584770421530757 4851421437484644454037017)
          ·
            refine ⟨3638566078113483340527763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4851421437484644454037017 3638566078113483340527763)
            ·
              refine ⟨5457849117170225010791645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3638566078113483340527763 5457849117170225010791645)
              ·
                refine ⟨2046693418938834379046867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5457849117170225010791645 2046693418938834379046867)
                ·
                  refine ⟨3070040128408251568570301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2046693418938834379046867 3070040128408251568570301)
                  ·
                    refine ⟨1151265048153094338213863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3070040128408251568570301 1151265048153094338213863)
                    ·
                      rfl

theorem cell22_3363121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 3, 1, 3].length) (baseStart_3363121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3363121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3363121 prefixEnd_3363121 := by exact prefixLift 3363121
  have htrace : WordTrace (prefixWord ++ tailWord_3363121) baseStart_3363121 baseEnd_3363121 := by
    simpa [prefixWord, tailWord_3363121, baseEnd_3363121] using wordTrace_append hprefix tailTrace_3363121
  have hstable : (prefixWord ++ tailWord_3363121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363121).length < 2 ^ (prefixWord ++ tailWord_3363121).sum := by decide
  have hdescent : baseEnd_3363121 < baseStart_3363121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363128 : List Nat := [2, 1, 2, 1, 3, 1, 2, 2, 8]
def baseStart_3363128 : Nat := 118140960795 + 3363128 * 2 ^ 59
def prefixEnd_3363128 : Nat := 4983230072969 + 3 ^ 40 * 3363128 * 2
def baseEnd_3363128 : Nat := 383755814798716217762947

theorem tailTrace_3363128 : CollatzResearch.WordTrace tailWord_3363128 prefixEnd_3363128 383755814798716217762947 := by
  unfold tailWord_3363128
  simp only [CollatzResearch.WordTrace]
  refine ⟨61331677679984553689529019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81775570239979404919372025 61331677679984553689529019)
  ·
    refine ⟨91997516519976830534293529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61331677679984553689529019 91997516519976830534293529)
    ·
      refine ⟨68998137389982622900720147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91997516519976830534293529 68998137389982622900720147)
      ·
        refine ⟨103497206084973934351080221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68998137389982622900720147 103497206084973934351080221)
        ·
          refine ⟨38811452281865225381655083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103497206084973934351080221 38811452281865225381655083)
          ·
            refine ⟨58217178422797838072482625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38811452281865225381655083 58217178422797838072482625)
            ·
              refine ⟨43662883817098378554361969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58217178422797838072482625 43662883817098378554361969)
              ·
                refine ⟨32747162862823783915771477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43662883817098378554361969 32747162862823783915771477)
                ·
                  refine ⟨383755814798716217762947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32747162862823783915771477 383755814798716217762947)
                  ·
                    rfl

theorem cell22_3363128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 8].length) (baseStart_3363128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3363128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3363128 prefixEnd_3363128 := by exact prefixLift 3363128
  have htrace : WordTrace (prefixWord ++ tailWord_3363128) baseStart_3363128 baseEnd_3363128 := by
    simpa [prefixWord, tailWord_3363128, baseEnd_3363128] using wordTrace_append hprefix tailTrace_3363128
  have hstable : (prefixWord ++ tailWord_3363128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363128).length < 2 ^ (prefixWord ++ tailWord_3363128).sum := by decide
  have hdescent : baseEnd_3363128 < baseStart_3363128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363160 : List Nat := [2, 1, 2, 2, 1, 1, 2, 2, 6, 3]
def baseStart_3363160 : Nat := 118140960795 + 3363160 * 2 ^ 59
def prefixEnd_3363160 : Nat := 4983230072969 + 3 ^ 40 * 3363160 * 2
def baseEnd_3363160 : Nat := 1151278398650111236488743

theorem tailTrace_3363160 : CollatzResearch.WordTrace tailWord_3363160 prefixEnd_3363160 1151278398650111236488743 := by
  unfold tailWord_3363160
  simp only [CollatzResearch.WordTrace]
  refine ⟨61332261247926588422111467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81776348330568784562815289 61332261247926588422111467)
  ·
    refine ⟨91998391871889882633167201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61332261247926588422111467 91998391871889882633167201)
    ·
      refine ⟨68998793903917411974875401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91998391871889882633167201 68998793903917411974875401)
      ·
        refine ⟨51749095427938058981156551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68998793903917411974875401 51749095427938058981156551)
        ·
          refine ⟨77623643141907088471734827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51749095427938058981156551 77623643141907088471734827)
          ·
            refine ⟨116435464712860632707602241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77623643141907088471734827 116435464712860632707602241)
            ·
              refine ⟨87326598534645474530701681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116435464712860632707602241 87326598534645474530701681)
              ·
                refine ⟨65494948900984105898026261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87326598534645474530701681 65494948900984105898026261)
                ·
                  refine ⟨3070075729733629963969981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 65494948900984105898026261 3070075729733629963969981)
                  ·
                    refine ⟨1151278398650111236488743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3070075729733629963969981 1151278398650111236488743)
                    ·
                      rfl

theorem cell22_3363160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 6, 3].length) (baseStart_3363160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3363160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3363160 prefixEnd_3363160 := by exact prefixLift 3363160
  have htrace : WordTrace (prefixWord ++ tailWord_3363160) baseStart_3363160 baseEnd_3363160 := by
    simpa [prefixWord, tailWord_3363160, baseEnd_3363160] using wordTrace_append hprefix tailTrace_3363160
  have hstable : (prefixWord ++ tailWord_3363160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363160).length < 2 ^ (prefixWord ++ tailWord_3363160).sum := by decide
  have hdescent : baseEnd_3363160 < baseStart_3363160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363164 : List Nat := [2, 2, 4, 3, 1, 1, 1, 1, 3, 4]
def baseStart_3363164 : Nat := 118140960795 + 3363164 * 2 ^ 59
def prefixEnd_3363164 : Nat := 4983230072969 + 3 ^ 40 * 3363164 * 2
def baseEnd_3363164 : Nat := 1151279767931856559388731

theorem tailTrace_3363164 : CollatzResearch.WordTrace tailWord_3363164 prefixEnd_3363164 1151279767931856559388731 := by
  unfold tailWord_3363164
  simp only [CollatzResearch.WordTrace]
  refine ⟨61332334193919342763684273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81776445591892457018245697 61332334193919342763684273)
  ·
    refine ⟨45999250645439507072763205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61332334193919342763684273 45999250645439507072763205)
    ·
      refine ⟨8624859496019907576143101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45999250645439507072763205 8624859496019907576143101)
      ·
        refine ⟨3234322311007465341053663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8624859496019907576143101 3234322311007465341053663)
        ·
          refine ⟨4851483466511198011580495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3234322311007465341053663 4851483466511198011580495)
          ·
            refine ⟨7277225199766797017370743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4851483466511198011580495 7277225199766797017370743)
            ·
              refine ⟨10915837799650195526056115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7277225199766797017370743 10915837799650195526056115)
              ·
                refine ⟨16373756699475293289084173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10915837799650195526056115 16373756699475293289084173)
                ·
                  refine ⟨6140158762303234983406565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16373756699475293289084173 6140158762303234983406565)
                  ·
                    refine ⟨1151279767931856559388731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6140158762303234983406565 1151279767931856559388731)
                    ·
                      rfl

theorem cell22_3363164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_3363164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3363164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3363164 prefixEnd_3363164 := by exact prefixLift 3363164
  have htrace : WordTrace (prefixWord ++ tailWord_3363164) baseStart_3363164 baseEnd_3363164 := by
    simpa [prefixWord, tailWord_3363164, baseEnd_3363164] using wordTrace_append hprefix tailTrace_3363164
  have hstable : (prefixWord ++ tailWord_3363164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363164).length < 2 ^ (prefixWord ++ tailWord_3363164).sum := by decide
  have hdescent : baseEnd_3363164 < baseStart_3363164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363250 : List Nat := [3, 2, 1, 1, 1, 1, 3, 1, 4, 5]
def baseStart_3363250 : Nat := 118140960795 + 3363250 * 2 ^ 59
def prefixEnd_3363250 : Nat := 4983230072969 + 3 ^ 40 * 3363250 * 2
def baseEnd_3363250 : Nat := 1151309207489381001738467

theorem tailTrace_3363250 : CollatzResearch.WordTrace tailWord_3363250 prefixEnd_3363250 1151309207489381001738467 := by
  unfold tailWord_3363250
  simp only [CollatzResearch.WordTrace]
  refine ⟨30666951266381780553749801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81778536710351414809999469 30666951266381780553749801)
  ·
    refine ⟨23000213449786335415312351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30666951266381780553749801 23000213449786335415312351)
    ·
      refine ⟨34500320174679503122968527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23000213449786335415312351 34500320174679503122968527)
      ·
        refine ⟨51750480262019254684452791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34500320174679503122968527 51750480262019254684452791)
        ·
          refine ⟨77625720393028882026679187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51750480262019254684452791 77625720393028882026679187)
          ·
            refine ⟨116438580589543323040018781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77625720393028882026679187 116438580589543323040018781)
            ·
              refine ⟨43664467721078746140007043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116438580589543323040018781 43664467721078746140007043)
              ·
                refine ⟨65496701581618119210010565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43664467721078746140007043 65496701581618119210010565)
                ·
                  refine ⟨12280631546553397351876981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65496701581618119210010565 12280631546553397351876981)
                  ·
                    refine ⟨1151309207489381001738467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12280631546553397351876981 1151309207489381001738467)
                    ·
                      rfl

theorem cell22_3363250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_3363250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3363250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3363250 prefixEnd_3363250 := by exact prefixLift 3363250
  have htrace : WordTrace (prefixWord ++ tailWord_3363250) baseStart_3363250 baseEnd_3363250 := by
    simpa [prefixWord, tailWord_3363250, baseEnd_3363250] using wordTrace_append hprefix tailTrace_3363250
  have hstable : (prefixWord ++ tailWord_3363250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363250).length < 2 ^ (prefixWord ++ tailWord_3363250).sum := by decide
  have hdescent : baseEnd_3363250 < baseStart_3363250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363312 : List Nat := [2, 1, 1, 1, 3, 3, 1, 3, 4, 3]
def baseStart_3363312 : Nat := 118140960795 + 3363312 * 2 ^ 59
def prefixEnd_3363312 : Nat := 4983230072969 + 3 ^ 40 * 3363312 * 2
def baseEnd_3363312 : Nat := 1151330431356433506688277

theorem tailTrace_3363312 : CollatzResearch.WordTrace tailWord_3363312 prefixEnd_3363312 1151330431356433506688277 := by
  unfold tailWord_3363312
  simp only [CollatzResearch.WordTrace]
  refine ⟨61335033195651253401878095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81780044260868337869170793 61335033195651253401878095)
  ·
    refine ⟨92002549793476880102817143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61335033195651253401878095 92002549793476880102817143)
    ·
      refine ⟨138003824690215320154225715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92002549793476880102817143 138003824690215320154225715)
      ·
        refine ⟨207005737035322980231338573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138003824690215320154225715 207005737035322980231338573)
        ·
          refine ⟨77627151388246117586751965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207005737035322980231338573 77627151388246117586751965)
          ·
            refine ⟨29110181770592294095031987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77627151388246117586751965 29110181770592294095031987)
            ·
              refine ⟨43665272655888441142547981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29110181770592294095031987 43665272655888441142547981)
              ·
                refine ⟨16374477245958165428455493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43665272655888441142547981 16374477245958165428455493)
                ·
                  refine ⟨3070214483617156017835405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16374477245958165428455493 3070214483617156017835405)
                  ·
                    refine ⟨1151330431356433506688277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3070214483617156017835405 1151330431356433506688277)
                    ·
                      rfl

theorem cell22_3363312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 4, 3].length) (baseStart_3363312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3363312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3363312 prefixEnd_3363312 := by exact prefixLift 3363312
  have htrace : WordTrace (prefixWord ++ tailWord_3363312) baseStart_3363312 baseEnd_3363312 := by
    simpa [prefixWord, tailWord_3363312, baseEnd_3363312] using wordTrace_append hprefix tailTrace_3363312
  have hstable : (prefixWord ++ tailWord_3363312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363312).length < 2 ^ (prefixWord ++ tailWord_3363312).sum := by decide
  have hdescent : baseEnd_3363312 < baseStart_3363312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363342 : List Nat := [4, 1, 1, 2, 3, 1, 2, 8]
def baseStart_3363342 : Nat := 118140960795 + 3363342 * 2 ^ 59
def prefixEnd_3363342 : Nat := 4983230072969 + 3 ^ 40 * 3363342 * 2
def baseEnd_3363342 : Nat := 127926744552169269826465

theorem tailTrace_3363342 : CollatzResearch.WordTrace tailWord_3363342 prefixEnd_3363342 127926744552169269826465 := by
  unfold tailWord_3363342
  simp only [CollatzResearch.WordTrace]
  refine ⟨15333895072649227740918535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81780773720795881284898853 15333895072649227740918535)
  ·
    refine ⟨23000842608973841611377803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15333895072649227740918535 23000842608973841611377803)
    ·
      refine ⟨34501263913460762417066705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23000842608973841611377803 34501263913460762417066705)
      ·
        refine ⟨25875947935095571812800029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34501263913460762417066705 25875947935095571812800029)
        ·
          refine ⟨9703480475660839429800011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25875947935095571812800029 9703480475660839429800011)
          ·
            refine ⟨14555220713491259144700017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9703480475660839429800011 14555220713491259144700017)
            ·
              refine ⟨10916415535118444358525013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14555220713491259144700017 10916415535118444358525013)
              ·
                refine ⟨127926744552169269826465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10916415535118444358525013 127926744552169269826465)
                ·
                  rfl

theorem cell22_3363342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 8].length) (baseStart_3363342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3363342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3363342 prefixEnd_3363342 := by exact prefixLift 3363342
  have htrace : WordTrace (prefixWord ++ tailWord_3363342) baseStart_3363342 baseEnd_3363342 := by
    simpa [prefixWord, tailWord_3363342, baseEnd_3363342] using wordTrace_append hprefix tailTrace_3363342
  have hstable : (prefixWord ++ tailWord_3363342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363342).length < 2 ^ (prefixWord ++ tailWord_3363342).sum := by decide
  have hdescent : baseEnd_3363342 < baseStart_3363342 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363355 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 6, 6]
def baseStart_3363355 : Nat := 118140960795 + 3363355 * 2 ^ 59
def prefixEnd_3363355 : Nat := 4983230072969 + 3 ^ 40 * 3363355 * 2
def baseEnd_3363355 : Nat := 1151345151135195727863145

theorem tailTrace_3363355 : CollatzResearch.WordTrace tailWord_3363355 prefixEnd_3363355 1151345151135195727863145 := by
  unfold tailWord_3363355
  simp only [CollatzResearch.WordTrace]
  refine ⟨122671634730146725147571519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81781089820097816765047679 122671634730146725147571519)
  ·
    refine ⟨184007452095220087721357279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122671634730146725147571519 184007452095220087721357279)
    ·
      refine ⟨276011178142830131582035919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184007452095220087721357279 276011178142830131582035919)
      ·
        refine ⟨414016767214245197373053879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276011178142830131582035919 414016767214245197373053879)
        ·
          refine ⟨621025150821367796059580819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414016767214245197373053879 621025150821367796059580819)
          ·
            refine ⟨931537726232051694089371229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 621025150821367796059580819 931537726232051694089371229)
            ·
              refine ⟨349326647337019385283514211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 931537726232051694089371229 349326647337019385283514211)
              ·
                refine ⟨523989971005529077925271317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 349326647337019385283514211 523989971005529077925271317)
                ·
                  refine ⟨24562029890884175527747093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 523989971005529077925271317 24562029890884175527747093)
                  ·
                    refine ⟨1151345151135195727863145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24562029890884175527747093 1151345151135195727863145)
                    ·
                      rfl

theorem cell22_3363355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 6].length) (baseStart_3363355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3363355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3363355 prefixEnd_3363355 := by exact prefixLift 3363355
  have htrace : WordTrace (prefixWord ++ tailWord_3363355) baseStart_3363355 baseEnd_3363355 := by
    simpa [prefixWord, tailWord_3363355, baseEnd_3363355] using wordTrace_append hprefix tailTrace_3363355
  have hstable : (prefixWord ++ tailWord_3363355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363355).length < 2 ^ (prefixWord ++ tailWord_3363355).sum := by decide
  have hdescent : baseEnd_3363355 < baseStart_3363355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363479 : List Nat := [1, 1, 3, 3, 2, 1, 3, 2, 2, 4]
def baseStart_3363479 : Nat := 118140960795 + 3363479 * 2 ^ 59
def prefixEnd_3363479 : Nat := 4983230072969 + 3 ^ 40 * 3363479 * 2
def baseEnd_3363479 : Nat := 1151387598869300737762765

theorem tailTrace_3363479 : CollatzResearch.WordTrace tailWord_3363479 prefixEnd_3363479 1151387598869300737762765 := by
  unfold tailWord_3363479
  simp only [CollatzResearch.WordTrace]
  refine ⟨122676157381697494325085491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81784104921131662883390327 122676157381697494325085491)
  ·
    refine ⟨184014236072546241487628237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122676157381697494325085491 184014236072546241487628237)
    ·
      refine ⟨69005338527204840557860589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184014236072546241487628237 69005338527204840557860589)
      ·
        refine ⟨25877001947701815209197721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69005338527204840557860589 25877001947701815209197721)
        ·
          refine ⟨19407751460776361406898291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25877001947701815209197721 19407751460776361406898291)
          ·
            refine ⟨29111627191164542110347437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19407751460776361406898291 29111627191164542110347437)
            ·
              refine ⟨10916860196686703291380289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29111627191164542110347437 10916860196686703291380289)
              ·
                refine ⟨8187645147515027468535217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10916860196686703291380289 8187645147515027468535217)
                ·
                  refine ⟨6140733860636270601401413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8187645147515027468535217 6140733860636270601401413)
                  ·
                    refine ⟨1151387598869300737762765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6140733860636270601401413 1151387598869300737762765)
                    ·
                      rfl

theorem cell22_3363479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 2, 2, 4].length) (baseStart_3363479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3363479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3363479 prefixEnd_3363479 := by exact prefixLift 3363479
  have htrace : WordTrace (prefixWord ++ tailWord_3363479) baseStart_3363479 baseEnd_3363479 := by
    simpa [prefixWord, tailWord_3363479, baseEnd_3363479] using wordTrace_append hprefix tailTrace_3363479
  have hstable : (prefixWord ++ tailWord_3363479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363479).length < 2 ^ (prefixWord ++ tailWord_3363479).sum := by decide
  have hdescent : baseEnd_3363479 < baseStart_3363479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363543 : List Nat := [1, 1, 3, 2, 1, 5, 1, 4, 1, 3]
def baseStart_3363543 : Nat := 118140960795 + 3363543 * 2 ^ 59
def prefixEnd_3363543 : Nat := 4983230072969 + 3 ^ 40 * 3363543 * 2
def baseEnd_3363543 : Nat := 1151409507377225904162569

theorem tailTrace_3363543 : CollatzResearch.WordTrace tailWord_3363543 prefixEnd_3363543 1151409507377225904162569 := by
  unfold tailWord_3363543
  simp only [CollatzResearch.WordTrace]
  refine ⟨122678491653465633255415283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81785661102310422170276855 122678491653465633255415283)
  ·
    refine ⟨184017737480198449883122925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122678491653465633255415283 184017737480198449883122925)
    ·
      refine ⟨69006651555074418706171097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184017737480198449883122925 69006651555074418706171097)
      ·
        refine ⟨51754988666305814029628323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69006651555074418706171097 51754988666305814029628323)
        ·
          refine ⟨77632482999458721044442485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51754988666305814029628323 77632482999458721044442485)
          ·
            refine ⟨7278045281199255097916483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77632482999458721044442485 7278045281199255097916483)
            ·
              refine ⟨10917067921798882646874725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7278045281199255097916483 10917067921798882646874725)
              ·
                refine ⟨2046950235337290496289011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10917067921798882646874725 2046950235337290496289011)
                ·
                  refine ⟨3070425353005935744433517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2046950235337290496289011 3070425353005935744433517)
                  ·
                    refine ⟨1151409507377225904162569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3070425353005935744433517 1151409507377225904162569)
                    ·
                      rfl

theorem cell22_3363543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 4, 1, 3].length) (baseStart_3363543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3363543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3363543 prefixEnd_3363543 := by exact prefixLift 3363543
  have htrace : WordTrace (prefixWord ++ tailWord_3363543) baseStart_3363543 baseEnd_3363543 := by
    simpa [prefixWord, tailWord_3363543, baseEnd_3363543] using wordTrace_append hprefix tailTrace_3363543
  have hstable : (prefixWord ++ tailWord_3363543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363543).length < 2 ^ (prefixWord ++ tailWord_3363543).sum := by decide
  have hdescent : baseEnd_3363543 < baseStart_3363543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363569 : List Nat := [1, 2, 2, 2, 2, 2, 1, 3, 3, 4]
def baseStart_3363569 : Nat := 118140960795 + 3363569 * 2 ^ 59
def prefixEnd_3363569 : Nat := 4983230072969 + 3 ^ 40 * 3363569 * 2
def baseEnd_3363569 : Nat := 1151418407708570503012489

theorem tailTrace_3363569 : CollatzResearch.WordTrace tailWord_3363569 prefixEnd_3363569 1151418407708570503012489 := by
  unfold tailWord_3363569
  simp only [CollatzResearch.WordTrace]
  refine ⟨122679439951371439695861761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81786293300914293130574507 122679439951371439695861761)
  ·
    refine ⟨92009579963528579771896321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122679439951371439695861761 92009579963528579771896321)
    ·
      refine ⟨69007184972646434828922241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92009579963528579771896321 69007184972646434828922241)
      ·
        refine ⟨51755388729484826121691681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69007184972646434828922241 51755388729484826121691681)
        ·
          refine ⟨38816541547113619591268761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51755388729484826121691681 38816541547113619591268761)
          ·
            refine ⟨29112406160335214693451571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38816541547113619591268761 29112406160335214693451571)
            ·
              refine ⟨43668609240502822040177357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29112406160335214693451571 43668609240502822040177357)
              ·
                refine ⟨16375728465188558265066509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43668609240502822040177357 16375728465188558265066509)
                ·
                  refine ⟨6140898174445709349399941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16375728465188558265066509 6140898174445709349399941)
                  ·
                    refine ⟨1151418407708570503012489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6140898174445709349399941 1151418407708570503012489)
                    ·
                      rfl

theorem cell22_3363569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 3, 4].length) (baseStart_3363569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3363569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3363569 prefixEnd_3363569 := by exact prefixLift 3363569
  have htrace : WordTrace (prefixWord ++ tailWord_3363569) baseStart_3363569 baseEnd_3363569 := by
    simpa [prefixWord, tailWord_3363569, baseEnd_3363569] using wordTrace_append hprefix tailTrace_3363569
  have hstable : (prefixWord ++ tailWord_3363569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363569).length < 2 ^ (prefixWord ++ tailWord_3363569).sum := by decide
  have hdescent : baseEnd_3363569 < baseStart_3363569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363601 : List Nat := [1, 2, 2, 1, 1, 3, 4, 4, 4]
def baseStart_3363601 : Nat := 118140960795 + 3363601 * 2 ^ 59
def prefixEnd_3363601 : Nat := 4983230072969 + 3 ^ 40 * 3363601 * 2
def baseEnd_3363601 : Nat := 383809787320844362070797

theorem tailTrace_3363601 : CollatzResearch.WordTrace tailWord_3363601 prefixEnd_3363601 383809787320844362070797 := by
  unfold tailWord_3363601
  simp only [CollatzResearch.WordTrace]
  refine ⟨122680607087255509161026657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81787071391503672774017771 122680607087255509161026657)
  ·
    refine ⟨92010455315441631870769993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122680607087255509161026657 92010455315441631870769993)
    ·
      refine ⟨69007841486581223903077495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92010455315441631870769993 69007841486581223903077495)
      ·
        refine ⟨103511762229871835854616243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69007841486581223903077495 103511762229871835854616243)
        ·
          refine ⟨155267643344807753781924365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103511762229871835854616243 155267643344807753781924365)
          ·
            refine ⟨58225366254302907668221637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155267643344807753781924365 58225366254302907668221637)
            ·
              refine ⟨10917256172681795187791557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58225366254302907668221637 10917256172681795187791557)
              ·
                refine ⟨2046985532377836597710917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10917256172681795187791557 2046985532377836597710917)
                ·
                  refine ⟨383809787320844362070797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2046985532377836597710917 383809787320844362070797)
                  ·
                    rfl

theorem cell22_3363601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 4, 4].length) (baseStart_3363601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3363601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3363601 prefixEnd_3363601 := by exact prefixLift 3363601
  have htrace : WordTrace (prefixWord ++ tailWord_3363601) baseStart_3363601 baseEnd_3363601 := by
    simpa [prefixWord, tailWord_3363601, baseEnd_3363601] using wordTrace_append hprefix tailTrace_3363601
  have hstable : (prefixWord ++ tailWord_3363601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363601).length < 2 ^ (prefixWord ++ tailWord_3363601).sum := by decide
  have hdescent : baseEnd_3363601 < baseStart_3363601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363616 : List Nat := [2, 1, 1, 5, 1, 2, 3, 1, 1, 5]
def baseStart_3363616 : Nat := 118140960795 + 3363616 * 2 ^ 59
def prefixEnd_3363616 : Nat := 4983230072969 + 3 ^ 40 * 3363616 * 2
def baseEnd_3363616 : Nat := 1151434496769078047087345

theorem tailTrace_3363616 : CollatzResearch.WordTrace tailWord_3363616 prefixEnd_3363616 1151434496769078047087345 := by
  unfold tailWord_3363616
  simp only [CollatzResearch.WordTrace]
  refine ⟨61340577091100583361411351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81787436121467444481881801 61340577091100583361411351)
  ·
    refine ⟨92010865636650875042117027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61340577091100583361411351 92010865636650875042117027)
    ·
      refine ⟨138016298454976312563175541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92010865636650875042117027 138016298454976312563175541)
      ·
        refine ⟨12939027980154029302797707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 138016298454976312563175541 12939027980154029302797707)
        ·
          refine ⟨19408541970231043954196561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12939027980154029302797707 19408541970231043954196561)
          ·
            refine ⟨14556406477673282965647421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19408541970231043954196561 14556406477673282965647421)
            ·
              refine ⟨5458652429127481112117783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14556406477673282965647421 5458652429127481112117783)
              ·
                refine ⟨8187978643691221668176675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5458652429127481112117783 8187978643691221668176675)
                ·
                  refine ⟨12281967965536832502265013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8187978643691221668176675 12281967965536832502265013)
                  ·
                    refine ⟨1151434496769078047087345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12281967965536832502265013 1151434496769078047087345)
                    ·
                      rfl

theorem cell22_3363616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 1, 1, 5].length) (baseStart_3363616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3363616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3363616 prefixEnd_3363616 := by exact prefixLift 3363616
  have htrace : WordTrace (prefixWord ++ tailWord_3363616) baseStart_3363616 baseEnd_3363616 := by
    simpa [prefixWord, tailWord_3363616, baseEnd_3363616] using wordTrace_append hprefix tailTrace_3363616
  have hstable : (prefixWord ++ tailWord_3363616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363616).length < 2 ^ (prefixWord ++ tailWord_3363616).sum := by decide
  have hdescent : baseEnd_3363616 < baseStart_3363616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363652 : List Nat := [2, 3, 4, 2, 2, 1, 1, 1, 6]
def baseStart_3363652 : Nat := 118140960795 + 3363652 * 2 ^ 59
def prefixEnd_3363652 : Nat := 4983230072969 + 3 ^ 40 * 3363652 * 2
def baseEnd_3363652 : Nat := 383815606768261984395745

theorem tailTrace_3363652 : CollatzResearch.WordTrace tailWord_3363652 prefixEnd_3363652 383815606768261984395745 := by
  unfold tailWord_3363652
  simp only [CollatzResearch.WordTrace]
  refine ⟨61341233605035372435566605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81788311473380496580755473 61341233605035372435566605)
  ·
    refine ⟨23002962601888264663337477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61341233605035372435566605 23002962601888264663337477)
    ·
      refine ⟨4313055487854049624375777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23002962601888264663337477 4313055487854049624375777)
      ·
        refine ⟨3234791615890537218281833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4313055487854049624375777 3234791615890537218281833)
        ·
          refine ⟨2426093711917902913711375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3234791615890537218281833 2426093711917902913711375)
          ·
            refine ⟨3639140567876854370567063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2426093711917902913711375 3639140567876854370567063)
            ·
              refine ⟨5458710851815281555850595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3639140567876854370567063 5458710851815281555850595)
              ·
                refine ⟨8188066277722922333775893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5458710851815281555850595 8188066277722922333775893)
                ·
                  refine ⟨383815606768261984395745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8188066277722922333775893 383815606768261984395745)
                  ·
                    rfl

theorem cell22_3363652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 1, 6].length) (baseStart_3363652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3363652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3363652 prefixEnd_3363652 := by exact prefixLift 3363652
  have htrace : WordTrace (prefixWord ++ tailWord_3363652) baseStart_3363652 baseEnd_3363652 := by
    simpa [prefixWord, tailWord_3363652, baseEnd_3363652] using wordTrace_append hprefix tailTrace_3363652
  have hstable : (prefixWord ++ tailWord_3363652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363652).length < 2 ^ (prefixWord ++ tailWord_3363652).sum := by decide
  have hdescent : baseEnd_3363652 < baseStart_3363652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363689 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 6, 5]
def baseStart_3363689 : Nat := 118140960795 + 3363689 * 2 ^ 59
def prefixEnd_3363689 : Nat := 4983230072969 + 3 ^ 40 * 3363689 * 2
def baseEnd_3363689 : Nat := 1151459486160930190012121

theorem tailTrace_3363689 : CollatzResearch.WordTrace tailWord_3363689 prefixEnd_3363689 1151459486160930190012121 := by
  unfold tailWord_3363689
  simp only [CollatzResearch.WordTrace]
  refine ⟨122683816710936700190230121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81789211140624466793486747 122683816710936700190230121)
  ·
    refine ⟨92012862533202525142672591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122683816710936700190230121 92012862533202525142672591)
    ·
      refine ⟨138019293799803787714008887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92012862533202525142672591 138019293799803787714008887)
      ·
        refine ⟨207028940699705681571013331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138019293799803787714008887 207028940699705681571013331)
        ·
          refine ⟨310543411049558522356519997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207028940699705681571013331 310543411049558522356519997)
          ·
            refine ⟨116453779143584445883694999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 310543411049558522356519997 116453779143584445883694999)
            ·
              refine ⟨174680668715376668825542499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116453779143584445883694999 174680668715376668825542499)
              ·
                refine ⟨262021003073065003238313749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174680668715376668825542499 262021003073065003238313749)
                ·
                  refine ⟨12282234519049922026795957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 262021003073065003238313749 12282234519049922026795957)
                  ·
                    refine ⟨1151459486160930190012121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12282234519049922026795957 1151459486160930190012121)
                    ·
                      rfl

theorem cell22_3363689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6, 5].length) (baseStart_3363689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3363689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3363689 prefixEnd_3363689 := by exact prefixLift 3363689
  have htrace : WordTrace (prefixWord ++ tailWord_3363689) baseStart_3363689 baseEnd_3363689 := by
    simpa [prefixWord, tailWord_3363689, baseEnd_3363689] using wordTrace_append hprefix tailTrace_3363689
  have hstable : (prefixWord ++ tailWord_3363689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363689).length < 2 ^ (prefixWord ++ tailWord_3363689).sum := by decide
  have hdescent : baseEnd_3363689 < baseStart_3363689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363721 : List Nat := [1, 2, 1, 1, 5, 2, 1, 2, 3, 4]
def baseStart_3363721 : Nat := 118140960795 + 3363721 * 2 ^ 59
def prefixEnd_3363721 : Nat := 4983230072969 + 3 ^ 40 * 3363721 * 2
def baseEnd_3363721 : Nat := 1151470440414892773212023

theorem tailTrace_3363721 : CollatzResearch.WordTrace tailWord_3363721 prefixEnd_3363721 1151470440414892773212023 := by
  unfold tailWord_3363721
  simp only [CollatzResearch.WordTrace]
  refine ⟨122684983846820769655395017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81789989231213846436930011 122684983846820769655395017)
  ·
    refine ⟨92013737885115577241546263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122684983846820769655395017 92013737885115577241546263)
    ·
      refine ⟨138020606827673365862319395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92013737885115577241546263 138020606827673365862319395)
      ·
        refine ⟨207030910241510048793479093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138020606827673365862319395 207030910241510048793479093)
        ·
          refine ⟨19409147835141567074388665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 207030910241510048793479093 19409147835141567074388665)
          ·
            refine ⟨14556860876356175305791499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19409147835141567074388665 14556860876356175305791499)
            ·
              refine ⟨21835291314534262958687249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14556860876356175305791499 21835291314534262958687249)
              ·
                refine ⟨16376468485900697219015437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21835291314534262958687249 16376468485900697219015437)
                ·
                  refine ⟨6141175682212761457130789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16376468485900697219015437 6141175682212761457130789)
                  ·
                    refine ⟨1151470440414892773212023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6141175682212761457130789 1151470440414892773212023)
                    ·
                      rfl

theorem cell22_3363721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 3, 4].length) (baseStart_3363721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3363721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3363721 prefixEnd_3363721 := by exact prefixLift 3363721
  have htrace : WordTrace (prefixWord ++ tailWord_3363721) baseStart_3363721 baseEnd_3363721 := by
    simpa [prefixWord, tailWord_3363721, baseEnd_3363721] using wordTrace_append hprefix tailTrace_3363721
  have hstable : (prefixWord ++ tailWord_3363721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363721).length < 2 ^ (prefixWord ++ tailWord_3363721).sum := by decide
  have hdescent : baseEnd_3363721 < baseStart_3363721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363753 : List Nat := [1, 2, 1, 1, 1, 1, 8, 3, 4]
def baseStart_3363753 : Nat := 118140960795 + 3363753 * 2 ^ 59
def prefixEnd_3363753 : Nat := 4983230072969 + 3 ^ 40 * 3363753 * 2
def baseEnd_3363753 : Nat := 383827131556285118803975

theorem tailTrace_3363753 : CollatzResearch.WordTrace tailWord_3363753 prefixEnd_3363753 383827131556285118803975 := by
  unfold tailWord_3363753
  simp only [CollatzResearch.WordTrace]
  refine ⟨122686150982704839120559913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81790767321803226080373275 122686150982704839120559913)
  ·
    refine ⟨92014613237028629340419935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122686150982704839120559913 92014613237028629340419935)
    ·
      refine ⟨138021919855542944010629903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92014613237028629340419935 138021919855542944010629903)
      ·
        refine ⟨207032879783314416015944855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138021919855542944010629903 207032879783314416015944855)
        ·
          refine ⟨310549319674971624023917283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207032879783314416015944855 310549319674971624023917283)
          ·
            refine ⟨465823979512457436035875925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310549319674971624023917283 465823979512457436035875925)
            ·
              refine ⟨5458874759911610578545421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 465823979512457436035875925 5458874759911610578545421)
              ·
                refine ⟨2047078034966853966954533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5458874759911610578545421 2047078034966853966954533)
                ·
                  refine ⟨383827131556285118803975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2047078034966853966954533 383827131556285118803975)
                  ·
                    rfl

theorem cell22_3363753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 3, 4].length) (baseStart_3363753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3363753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3363753 prefixEnd_3363753 := by exact prefixLift 3363753
  have htrace : WordTrace (prefixWord ++ tailWord_3363753) baseStart_3363753 baseEnd_3363753 := by
    simpa [prefixWord, tailWord_3363753, baseEnd_3363753] using wordTrace_append hprefix tailTrace_3363753
  have hstable : (prefixWord ++ tailWord_3363753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363753).length < 2 ^ (prefixWord ++ tailWord_3363753).sum := by decide
  have hdescent : baseEnd_3363753 < baseStart_3363753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363768 : List Nat := [2, 1, 2, 1, 2, 5, 1, 1, 4, 3]
def baseStart_3363768 : Nat := 118140960795 + 3363768 * 2 ^ 59
def prefixEnd_3363768 : Nat := 4983230072969 + 3 ^ 40 * 3363768 * 2
def baseEnd_3363768 : Nat := 1151486529475400317286879

theorem tailTrace_3363768 : CollatzResearch.WordTrace tailWord_3363768 prefixEnd_3363768 1151486529475400317286879 := by
  unfold tailWord_3363768
  simp only [CollatzResearch.WordTrace]
  refine ⟨61343349038825248341177979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81791132051766997788237305 61343349038825248341177979)
  ·
    refine ⟨92015023558237872511766969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61343349038825248341177979 92015023558237872511766969)
    ·
      refine ⟨69011267668678404383825227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92015023558237872511766969 69011267668678404383825227)
      ·
        refine ⟨103516901503017606575737841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69011267668678404383825227 103516901503017606575737841)
        ·
          refine ⟨77637676127263204931803381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103516901503017606575737841 77637676127263204931803381)
          ·
            refine ⟨7278532136930925462356567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77637676127263204931803381 7278532136930925462356567)
            ·
              refine ⟨10917798205396388193534851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7278532136930925462356567 10917798205396388193534851)
              ·
                refine ⟨16376697308094582290302277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10917798205396388193534851 16376697308094582290302277)
                ·
                  refine ⟨3070630745267734179431677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16376697308094582290302277 3070630745267734179431677)
                  ·
                    refine ⟨1151486529475400317286879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3070630745267734179431677 1151486529475400317286879)
                    ·
                      rfl

theorem cell22_3363768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 4, 3].length) (baseStart_3363768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3363768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3363768 prefixEnd_3363768 := by exact prefixLift 3363768
  have htrace : WordTrace (prefixWord ++ tailWord_3363768) baseStart_3363768 baseEnd_3363768 := by
    simpa [prefixWord, tailWord_3363768, baseEnd_3363768] using wordTrace_append hprefix tailTrace_3363768
  have hstable : (prefixWord ++ tailWord_3363768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363768).length < 2 ^ (prefixWord ++ tailWord_3363768).sum := by decide
  have hdescent : baseEnd_3363768 < baseStart_3363768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363903 : List Nat := [1, 1, 2, 2, 3, 1, 1, 2, 6, 3]
def baseStart_3363903 : Nat := 118140960795 + 3363903 * 2 ^ 59
def prefixEnd_3363903 : Nat := 4983230072969 + 3 ^ 40 * 3363903 * 2
def baseEnd_3363903 : Nat := 1151532742734304965161465

theorem tailTrace_3363903 : CollatzResearch.WordTrace tailWord_3363903 prefixEnd_3363903 1151532742734304965161465 := by
  unfold tailWord_3363903
  simp only [CollatzResearch.WordTrace]
  refine ⟨122691621932161414738520363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81794414621440943159013575 122691621932161414738520363)
  ·
    refine ⟨184037432898242122107780545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122691621932161414738520363 184037432898242122107780545)
    ·
      refine ⟨138028074673681591580835409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184037432898242122107780545 138028074673681591580835409)
      ·
        refine ⟨103521056005261193685626557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138028074673681591580835409 103521056005261193685626557)
        ·
          refine ⟨38820396001972947632109959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103521056005261193685626557 38820396001972947632109959)
          ·
            refine ⟨58230594002959421448164939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38820396001972947632109959 58230594002959421448164939)
            ·
              refine ⟨87345891004439132172247409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58230594002959421448164939 87345891004439132172247409)
              ·
                refine ⟨65509418253329349129185557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87345891004439132172247409 65509418253329349129185557)
                ·
                  refine ⟨3070753980624813240430573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 65509418253329349129185557 3070753980624813240430573)
                  ·
                    refine ⟨1151532742734304965161465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3070753980624813240430573 1151532742734304965161465)
                    ·
                      rfl

theorem cell22_3363903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 6, 3].length) (baseStart_3363903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3363903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3363903 prefixEnd_3363903 := by exact prefixLift 3363903
  have htrace : WordTrace (prefixWord ++ tailWord_3363903) baseStart_3363903 baseEnd_3363903 := by
    simpa [prefixWord, tailWord_3363903, baseEnd_3363903] using wordTrace_append hprefix tailTrace_3363903
  have hstable : (prefixWord ++ tailWord_3363903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363903).length < 2 ^ (prefixWord ++ tailWord_3363903).sum := by decide
  have hdescent : baseEnd_3363903 < baseStart_3363903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363905 : List Nat := [1, 2, 5, 1, 3, 1, 1, 2, 6]
def baseStart_3363905 : Nat := 118140960795 + 3363905 * 2 ^ 59
def prefixEnd_3363905 : Nat := 4983230072969 + 3 ^ 40 * 3363905 * 2
def baseEnd_3363905 : Nat := 383844475791725875537153

theorem tailTrace_3363905 : CollatzResearch.WordTrace tailWord_3363905 prefixEnd_3363905 383844475791725875537153 := by
  unfold tailWord_3363905
  simp only [CollatzResearch.WordTrace]
  refine ⟨122691694878154169080093169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81794463252102779386728779 122691694878154169080093169)
  ·
    refine ⟨92018771158615626810069877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122691694878154169080093169 92018771158615626810069877)
    ·
      refine ⟨8626759796120215013444051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92018771158615626810069877 8626759796120215013444051)
      ·
        refine ⟨12940139694180322520166077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8626759796120215013444051 12940139694180322520166077)
        ·
          refine ⟨4852552385317620945062279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12940139694180322520166077 4852552385317620945062279)
          ·
            refine ⟨7278828577976431417593419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4852552385317620945062279 7278828577976431417593419)
            ·
              refine ⟨10918242866964647126390129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7278828577976431417593419 10918242866964647126390129)
              ·
                refine ⟨8188682150223485344792597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10918242866964647126390129 8188682150223485344792597)
                ·
                  refine ⟨383844475791725875537153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8188682150223485344792597 383844475791725875537153)
                  ·
                    rfl

theorem cell22_3363905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 2, 6].length) (baseStart_3363905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3363905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3363905 prefixEnd_3363905 := by exact prefixLift 3363905
  have htrace : WordTrace (prefixWord ++ tailWord_3363905) baseStart_3363905 baseEnd_3363905 := by
    simpa [prefixWord, tailWord_3363905, baseEnd_3363905] using wordTrace_append hprefix tailTrace_3363905
  have hstable : (prefixWord ++ tailWord_3363905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363905).length < 2 ^ (prefixWord ++ tailWord_3363905).sum := by decide
  have hdescent : baseEnd_3363905 < baseStart_3363905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363918 : List Nat := [4, 1, 1, 1, 1, 3, 3, 1, 1, 6]
def baseStart_3363918 : Nat := 118140960795 + 3363918 * 2 ^ 59
def prefixEnd_3363918 : Nat := 4983230072969 + 3 ^ 40 * 3363918 * 2
def baseEnd_3363918 : Nat := 1151537877540849926036419

theorem tailTrace_3363918 : CollatzResearch.WordTrace tailWord_3363918 prefixEnd_3363918 1151537877540849926036419 := by
  unfold tailWord_3363918
  simp only [CollatzResearch.WordTrace]
  refine ⟨15336521128388384037539551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81794779351404714866877605 15336521128388384037539551)
  ·
    refine ⟨23004781692582576056309327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15336521128388384037539551 23004781692582576056309327)
    ·
      refine ⟨34507172538873864084463991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23004781692582576056309327 34507172538873864084463991)
      ·
        refine ⟨51760758808310796126695987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34507172538873864084463991 51760758808310796126695987)
        ·
          refine ⟨77641138212466194190043981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51760758808310796126695987 77641138212466194190043981)
          ·
            refine ⟨29115426829674822821266493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77641138212466194190043981 29115426829674822821266493)
            ·
              refine ⟨10918285061128058557974935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29115426829674822821266493 10918285061128058557974935)
              ·
                refine ⟨16377427591692087836962403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10918285061128058557974935 16377427591692087836962403)
                ·
                  refine ⟨24566141387538131755443605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16377427591692087836962403 24566141387538131755443605)
                  ·
                    refine ⟨1151537877540849926036419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24566141387538131755443605 1151537877540849926036419)
                    ·
                      rfl

theorem cell22_3363918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_3363918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3363918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3363918 prefixEnd_3363918 := by exact prefixLift 3363918
  have htrace : WordTrace (prefixWord ++ tailWord_3363918) baseStart_3363918 baseEnd_3363918 := by
    simpa [prefixWord, tailWord_3363918, baseEnd_3363918] using wordTrace_append hprefix tailTrace_3363918
  have hstable : (prefixWord ++ tailWord_3363918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363918).length < 2 ^ (prefixWord ++ tailWord_3363918).sum := by decide
  have hdescent : baseEnd_3363918 < baseStart_3363918 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363922 : List Nat := [3, 2, 2, 1, 3, 2, 2, 3, 4]
def baseStart_3363922 : Nat := 118140960795 + 3363922 * 2 ^ 59
def prefixEnd_3363922 : Nat := 4983230072969 + 3 ^ 40 * 3363922 * 2
def baseEnd_3363922 : Nat := 383846415607531749645469

theorem tailTrace_3363922 : CollatzResearch.WordTrace tailWord_3363922 prefixEnd_3363922 383846415607531749645469 := by
  unfold tailWord_3363922
  simp only [CollatzResearch.WordTrace]
  refine ⟨30673078729773145245865505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81794876612728387322308013 30673078729773145245865505)
  ·
    refine ⟨23004809047329858934399129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30673078729773145245865505 23004809047329858934399129)
    ·
      refine ⟨17253606785497394200799347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23004809047329858934399129 17253606785497394200799347)
      ·
        refine ⟨25880410178246091301199021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17253606785497394200799347 25880410178246091301199021)
        ·
          refine ⟨9705153816842284237949633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25880410178246091301199021 9705153816842284237949633)
          ·
            refine ⟨7278865362631713178462225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9705153816842284237949633 7278865362631713178462225)
            ·
              refine ⟨5459149021973784883846669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7278865362631713178462225 5459149021973784883846669)
              ·
                refine ⟨2047180883240169331442501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5459149021973784883846669 2047180883240169331442501)
                ·
                  refine ⟨383846415607531749645469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2047180883240169331442501 383846415607531749645469)
                  ·
                    rfl

theorem cell22_3363922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 3, 4].length) (baseStart_3363922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3363922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3363922 prefixEnd_3363922 := by exact prefixLift 3363922
  have htrace : WordTrace (prefixWord ++ tailWord_3363922) baseStart_3363922 baseEnd_3363922 := by
    simpa [prefixWord, tailWord_3363922, baseEnd_3363922] using wordTrace_append hprefix tailTrace_3363922
  have hstable : (prefixWord ++ tailWord_3363922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363922).length < 2 ^ (prefixWord ++ tailWord_3363922).sum := by decide
  have hdescent : baseEnd_3363922 < baseStart_3363922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363965 : List Nat := [1, 4, 1, 1, 3, 1, 1, 4, 3, 3]
def baseStart_3363965 : Nat := 118140960795 + 3363965 * 2 ^ 59
def prefixEnd_3363965 : Nat := 4983230072969 + 3 ^ 40 * 3363965 * 2
def baseEnd_3363965 : Nat := 1151553966601357470111275

theorem tailTrace_3363965 : CollatzResearch.WordTrace tailWord_3363965 prefixEnd_3363965 1151553966601357470111275 := by
  unfold tailWord_3363965
  simp only [CollatzResearch.WordTrace]
  refine ⟨122693883257936799327277349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81795922171957866218184899 122693883257936799327277349)
  ·
    refine ⟨23005103110863149873864503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122693883257936799327277349 23005103110863149873864503)
    ·
      refine ⟨34507654666294724810796755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23005103110863149873864503 34507654666294724810796755)
      ·
        refine ⟨51761481999442087216195133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34507654666294724810796755 51761481999442087216195133)
        ·
          refine ⟨19410555749790782706073175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51761481999442087216195133 19410555749790782706073175)
          ·
            refine ⟨29115833624686174059109763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19410555749790782706073175 29115833624686174059109763)
            ·
              refine ⟨43673750437029261088664645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29115833624686174059109763 43673750437029261088664645)
              ·
                refine ⟨8188828206942986454124621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43673750437029261088664645 8188828206942986454124621)
                ·
                  refine ⟨3070810577603619920296733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8188828206942986454124621 3070810577603619920296733)
                  ·
                    refine ⟨1151553966601357470111275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3070810577603619920296733 1151553966601357470111275)
                    ·
                      rfl

theorem cell22_3363965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 4, 3, 3].length) (baseStart_3363965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3363965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3363965 prefixEnd_3363965 := by exact prefixLift 3363965
  have htrace : WordTrace (prefixWord ++ tailWord_3363965) baseStart_3363965 baseEnd_3363965 := by
    simpa [prefixWord, tailWord_3363965, baseEnd_3363965] using wordTrace_append hprefix tailTrace_3363965
  have hstable : (prefixWord ++ tailWord_3363965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363965).length < 2 ^ (prefixWord ++ tailWord_3363965).sum := by decide
  have hdescent : baseEnd_3363965 < baseStart_3363965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363978 : List Nat := [3, 1, 2, 3, 1, 1, 1, 1, 9]
def baseStart_3363978 : Nat := 118140960795 + 3363978 * 2 ^ 59
def prefixEnd_3363978 : Nat := 4983230072969 + 3 ^ 40 * 3363978 * 2
def baseEnd_3363978 : Nat := 383852805589009923178745

theorem tailTrace_3363978 : CollatzResearch.WordTrace tailWord_3363978 prefixEnd_3363978 383852805589009923178745 := by
  unfold tailWord_3363978
  simp only [CollatzResearch.WordTrace]
  refine ⟨30673589351722425636875147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81796238271259801698333725 30673589351722425636875147)
  ·
    refine ⟨46010384027583638455312721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30673589351722425636875147 46010384027583638455312721)
    ·
      refine ⟨34507788020687728841484541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46010384027583638455312721 34507788020687728841484541)
      ·
        refine ⟨12940420507757898315556703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34507788020687728841484541 12940420507757898315556703)
        ·
          refine ⟨19410630761636847473335055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12940420507757898315556703 19410630761636847473335055)
          ·
            refine ⟨29115946142455271210002583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19410630761636847473335055 29115946142455271210002583)
            ·
              refine ⟨43673919213682906815003875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29115946142455271210002583 43673919213682906815003875)
              ·
                refine ⟨65510878820524360222505813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43673919213682906815003875 65510878820524360222505813)
                ·
                  refine ⟨383852805589009923178745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 65510878820524360222505813 383852805589009923178745)
                  ·
                    rfl

theorem cell22_3363978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 9].length) (baseStart_3363978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3363978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3363978 prefixEnd_3363978 := by exact prefixLift 3363978
  have htrace : WordTrace (prefixWord ++ tailWord_3363978) baseStart_3363978 baseEnd_3363978 := by
    simpa [prefixWord, tailWord_3363978, baseEnd_3363978] using wordTrace_append hprefix tailTrace_3363978
  have hstable : (prefixWord ++ tailWord_3363978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363978).length < 2 ^ (prefixWord ++ tailWord_3363978).sum := by decide
  have hdescent : baseEnd_3363978 < baseStart_3363978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363999 : List Nat := [1, 1, 2, 6, 2, 2, 1, 1, 3, 3]
def baseStart_3363999 : Nat := 118140960795 + 3363999 * 2 ^ 59
def prefixEnd_3363999 : Nat := 4983230072969 + 3 ^ 40 * 3363999 * 2
def baseEnd_3363999 : Nat := 1151565605496192714761171

theorem tailTrace_3363999 : CollatzResearch.WordTrace tailWord_3363999 prefixEnd_3363999 1151565605496192714761171 := by
  unfold tailWord_3363999
  simp only [CollatzResearch.WordTrace]
  refine ⟨122695123339813623134015051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81796748893209082089343367 122695123339813623134015051)
  ·
    refine ⟨184042685009720434701022577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122695123339813623134015051 184042685009720434701022577)
    ·
      refine ⟨138032013757290326025766933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184042685009720434701022577 138032013757290326025766933)
      ·
        refine ⟨6470250644872984032457825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 138032013757290326025766933 6470250644872984032457825)
        ·
          refine ⟨4852687983654738024343369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6470250644872984032457825 4852687983654738024343369)
          ·
            refine ⟨3639515987741053518257527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4852687983654738024343369 3639515987741053518257527)
            ·
              refine ⟨5459273981611580277386291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3639515987741053518257527 5459273981611580277386291)
              ·
                refine ⟨8188910972417370416079437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5459273981611580277386291 8188910972417370416079437)
                ·
                  refine ⟨3070841614656513906029789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8188910972417370416079437 3070841614656513906029789)
                  ·
                    refine ⟨1151565605496192714761171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3070841614656513906029789 1151565605496192714761171)
                    ·
                      rfl

theorem cell22_3363999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 1, 3, 3].length) (baseStart_3363999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3363999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3363999 prefixEnd_3363999 := by exact prefixLift 3363999
  have htrace : WordTrace (prefixWord ++ tailWord_3363999) baseStart_3363999 baseEnd_3363999 := by
    simpa [prefixWord, tailWord_3363999, baseEnd_3363999] using wordTrace_append hprefix tailTrace_3363999
  have hstable : (prefixWord ++ tailWord_3363999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363999).length < 2 ^ (prefixWord ++ tailWord_3363999).sum := by decide
  have hdescent : baseEnd_3363999 < baseStart_3363999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364023 : List Nat := [1, 1, 3, 1, 4, 1, 2, 1, 8]
def baseStart_3364023 : Nat := 118140960795 + 3364023 * 2 ^ 59
def prefixEnd_3364023 : Nat := 4983230072969 + 3 ^ 40 * 3364023 * 2
def baseEnd_3364023 : Nat := 383857940395554884053699

theorem tailTrace_3364023 : CollatzResearch.WordTrace tailWord_3364023 prefixEnd_3364023 383857940395554884053699 := by
  unfold tailWord_3364023
  simp only [CollatzResearch.WordTrace]
  refine ⟨122695998691726675232888723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81797332461151116821925815 122695998691726675232888723)
  ·
    refine ⟨184043998037590012849333085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122695998691726675232888723 184043998037590012849333085)
    ·
      refine ⟨69016499264096254818499907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184043998037590012849333085 69016499264096254818499907)
      ·
        refine ⟨103524748896144382227749861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69016499264096254818499907 103524748896144382227749861)
        ·
          refine ⟨19410890418027071667703099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103524748896144382227749861 19410890418027071667703099)
          ·
            refine ⟨29116335627040607501554649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19410890418027071667703099 29116335627040607501554649)
            ·
              refine ⟨21837251720280455626165987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29116335627040607501554649 21837251720280455626165987)
              ·
                refine ⟨32755877580420683439248981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21837251720280455626165987 32755877580420683439248981)
                ·
                  refine ⟨383857940395554884053699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32755877580420683439248981 383857940395554884053699)
                  ·
                    rfl

theorem cell22_3364023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 8].length) (baseStart_3364023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3364023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3364023 prefixEnd_3364023 := by exact prefixLift 3364023
  have htrace : WordTrace (prefixWord ++ tailWord_3364023) baseStart_3364023 baseEnd_3364023 := by
    simpa [prefixWord, tailWord_3364023, baseEnd_3364023] using wordTrace_append hprefix tailTrace_3364023
  have hstable : (prefixWord ++ tailWord_3364023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364023).length < 2 ^ (prefixWord ++ tailWord_3364023).sum := by decide
  have hdescent : baseEnd_3364023 < baseStart_3364023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364025 : List Nat := [1, 2, 1, 4, 1, 4, 1, 1, 3, 4]
def baseStart_3364025 : Nat := 118140960795 + 3364025 * 2 ^ 59
def prefixEnd_3364025 : Nat := 4983230072969 + 3 ^ 40 * 3364025 * 2
def baseEnd_3364025 : Nat := 1151574505827537313611091

theorem tailTrace_3364025 : CollatzResearch.WordTrace tailWord_3364025 prefixEnd_3364025 1151574505827537313611091 := by
  unfold tailWord_3364025
  simp only [CollatzResearch.WordTrace]
  refine ⟨122696071637719429574461529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81797381091812953049641019 122696071637719429574461529)
  ·
    refine ⟨92022053728289572180846147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122696071637719429574461529 92022053728289572180846147)
    ·
      refine ⟨138033080592434358271269221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92022053728289572180846147 138033080592434358271269221)
      ·
        refine ⟨25881202611081442175862979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138033080592434358271269221 25881202611081442175862979)
        ·
          refine ⟨38821803916622163263794469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25881202611081442175862979 38821803916622163263794469)
          ·
            refine ⟨7279088234366655611961463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38821803916622163263794469 7279088234366655611961463)
            ·
              refine ⟨10918632351549983417942195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7279088234366655611961463 10918632351549983417942195)
              ·
                refine ⟨16377948527324975126913293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10918632351549983417942195 16377948527324975126913293)
                ·
                  refine ⟨6141730697746865672592485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16377948527324975126913293 6141730697746865672592485)
                  ·
                    refine ⟨1151574505827537313611091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6141730697746865672592485 1151574505827537313611091)
                    ·
                      rfl

theorem cell22_3364025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 3, 4].length) (baseStart_3364025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3364025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3364025 prefixEnd_3364025 := by exact prefixLift 3364025
  have htrace : WordTrace (prefixWord ++ tailWord_3364025) baseStart_3364025 baseEnd_3364025 := by
    simpa [prefixWord, tailWord_3364025, baseEnd_3364025] using wordTrace_append hprefix tailTrace_3364025
  have hstable : (prefixWord ++ tailWord_3364025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364025).length < 2 ^ (prefixWord ++ tailWord_3364025).sum := by decide
  have hdescent : baseEnd_3364025 < baseStart_3364025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364055 : List Nat := [1, 1, 3, 2, 1, 2, 2, 3, 4, 3]
def baseStart_3364055 : Nat := 118140960795 + 3364055 * 2 ^ 59
def prefixEnd_3364055 : Nat := 4983230072969 + 3 ^ 40 * 3364055 * 2
def baseEnd_3364055 : Nat := 1151584775440627235360999

theorem tailTrace_3364055 : CollatzResearch.WordTrace tailWord_3364055 prefixEnd_3364055 1151584775440627235360999 := by
  unfold tailWord_3364055
  simp only [CollatzResearch.WordTrace]
  refine ⟨122697165827610744698053619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81798110551740496465369079 122697165827610744698053619)
  ·
    refine ⟨184045748741416117047080429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122697165827610744698053619 184045748741416117047080429)
    ·
      refine ⟨69017155778031043892655161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184045748741416117047080429 69017155778031043892655161)
      ·
        refine ⟨51762866833523282919491371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69017155778031043892655161 51762866833523282919491371)
        ·
          refine ⟨77644300250284924379237057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51762866833523282919491371 77644300250284924379237057)
          ·
            refine ⟨58233225187713693284427793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77644300250284924379237057 58233225187713693284427793)
            ·
              refine ⟨43674918890785269963320845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58233225187713693284427793 43674918890785269963320845)
              ·
                refine ⟨16378094584044476236245317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43674918890785269963320845 16378094584044476236245317)
                ·
                  refine ⟨3070892734508339294295997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16378094584044476236245317 3070892734508339294295997)
                  ·
                    refine ⟨1151584775440627235360999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3070892734508339294295997 1151584775440627235360999)
                    ·
                      rfl

theorem cell22_3364055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 4, 3].length) (baseStart_3364055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3364055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3364055 prefixEnd_3364055 := by exact prefixLift 3364055
  have htrace : WordTrace (prefixWord ++ tailWord_3364055) baseStart_3364055 baseEnd_3364055 := by
    simpa [prefixWord, tailWord_3364055, baseEnd_3364055] using wordTrace_append hprefix tailTrace_3364055
  have hstable : (prefixWord ++ tailWord_3364055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364055).length < 2 ^ (prefixWord ++ tailWord_3364055).sum := by decide
  have hdescent : baseEnd_3364055 < baseStart_3364055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364072 : List Nat := [2, 1, 4, 1, 2, 1, 1, 5, 2, 3]
def baseStart_3364072 : Nat := 118140960795 + 3364072 * 2 ^ 59
def prefixEnd_3364072 : Nat := 4983230072969 + 3 ^ 40 * 3364072 * 2
def baseEnd_3364072 : Nat := 1151590594888044857685947

theorem tailTrace_3364072 : CollatzResearch.WordTrace tailWord_3364072 prefixEnd_3364072 1151590594888044857685947 := by
  unfold tailWord_3364072
  simp only [CollatzResearch.WordTrace]
  refine ⟨61348892934274578300711235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81798523912366104400948313 61348892934274578300711235)
  ·
    refine ⟨92023339401411867451066853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61348892934274578300711235 92023339401411867451066853)
    ·
      refine ⟨17254376137764725147075035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92023339401411867451066853 17254376137764725147075035)
      ·
        refine ⟨25881564206647087720612553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17254376137764725147075035 25881564206647087720612553)
        ·
          refine ⟨19411173154985315790459415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25881564206647087720612553 19411173154985315790459415)
          ·
            refine ⟨29116759732477973685689123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19411173154985315790459415 29116759732477973685689123)
            ·
              refine ⟨43675139598716960528533685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29116759732477973685689123 43675139598716960528533685)
              ·
                refine ⟨4094544337379715049550033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43675139598716960528533685 4094544337379715049550033)
                ·
                  refine ⟨3070908253034786287162525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4094544337379715049550033 3070908253034786287162525)
                  ·
                    refine ⟨1151590594888044857685947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3070908253034786287162525 1151590594888044857685947)
                    ·
                      rfl

theorem cell22_3364072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_3364072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3364072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3364072 prefixEnd_3364072 := by exact prefixLift 3364072
  have htrace : WordTrace (prefixWord ++ tailWord_3364072) baseStart_3364072 baseEnd_3364072 := by
    simpa [prefixWord, tailWord_3364072, baseEnd_3364072] using wordTrace_append hprefix tailTrace_3364072
  have hstable : (prefixWord ++ tailWord_3364072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364072).length < 2 ^ (prefixWord ++ tailWord_3364072).sum := by decide
  have hdescent : baseEnd_3364072 < baseStart_3364072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364312 : List Nat := [2, 1, 2, 2, 2, 1, 2, 3, 3, 4]
def baseStart_3364312 : Nat := 118140960795 + 3364312 * 2 ^ 59
def prefixEnd_3364312 : Nat := 4983230072969 + 3 ^ 40 * 3364312 * 2
def baseEnd_3364312 : Nat := 1151672751792764231685211

theorem tailTrace_3364312 : CollatzResearch.WordTrace tailWord_3364312 prefixEnd_3364312 1151672751792764231685211 := by
  unfold tailWord_3364312
  simp only [CollatzResearch.WordTrace]
  refine ⟨61353269693839838795079595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81804359591786451726772793 61353269693839838795079595)
  ·
    refine ⟨92029904540759758192619393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61353269693839838795079595 92029904540759758192619393)
    ·
      refine ⟨69022428405569818644464545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92029904540759758192619393 69022428405569818644464545)
      ·
        refine ⟨51766821304177363983348409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69022428405569818644464545 51766821304177363983348409)
        ·
          refine ⟨38825115978133022987511307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51766821304177363983348409 38825115978133022987511307)
          ·
            refine ⟨58237673967199534481266961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38825115978133022987511307 58237673967199534481266961)
            ·
              refine ⟨43678255475399650860950221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58237673967199534481266961 43678255475399650860950221)
              ·
                refine ⟨16379345803274869072856333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43678255475399650860950221 16379345803274869072856333)
                ·
                  refine ⟨6142254676228075902321125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16379345803274869072856333 6142254676228075902321125)
                  ·
                    refine ⟨1151672751792764231685211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6142254676228075902321125 1151672751792764231685211)
                    ·
                      rfl

theorem cell22_3364312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 3, 4].length) (baseStart_3364312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3364312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3364312 prefixEnd_3364312 := by exact prefixLift 3364312
  have htrace : WordTrace (prefixWord ++ tailWord_3364312) baseStart_3364312 baseEnd_3364312 := by
    simpa [prefixWord, tailWord_3364312, baseEnd_3364312] using wordTrace_append hprefix tailTrace_3364312
  have hstable : (prefixWord ++ tailWord_3364312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364312).length < 2 ^ (prefixWord ++ tailWord_3364312).sum := by decide
  have hdescent : baseEnd_3364312 < baseStart_3364312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364344 : List Nat := [2, 1, 2, 1, 1, 7, 1, 1, 6]
def baseStart_3364344 : Nat := 118140960795 + 3364344 * 2 ^ 59
def prefixEnd_3364344 : Nat := 4983230072969 + 3 ^ 40 * 3364344 * 2
def baseEnd_3364344 : Nat := 383894568682242271628371

theorem tailTrace_3364344 : CollatzResearch.WordTrace tailWord_3364344 prefixEnd_3364344 383894568682242271628371 := by
  unfold tailWord_3364344
  simp only [CollatzResearch.WordTrace]
  refine ⟨61353853261781873527662043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81805137682375831370216057 61353853261781873527662043)
  ·
    refine ⟨92030779892672810291493065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61353853261781873527662043 92030779892672810291493065)
    ·
      refine ⟨69023084919504607718619799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92030779892672810291493065 69023084919504607718619799)
      ·
        refine ⟨103534627379256911577929699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69023084919504607718619799 103534627379256911577929699)
        ·
          refine ⟨155301941068885367366894549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103534627379256911577929699 155301941068885367366894549)
          ·
            refine ⟨3639889243802000797661591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 155301941068885367366894549 3639889243802000797661591)
            ·
              refine ⟨5459833865703001196492387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3639889243802000797661591 5459833865703001196492387)
              ·
                refine ⟨8189750798554501794738581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5459833865703001196492387 8189750798554501794738581)
                ·
                  refine ⟨383894568682242271628371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8189750798554501794738581 383894568682242271628371)
                  ·
                    rfl

theorem cell22_3364344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 1, 6].length) (baseStart_3364344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3364344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3364344 prefixEnd_3364344 := by exact prefixLift 3364344
  have htrace : WordTrace (prefixWord ++ tailWord_3364344) baseStart_3364344 baseEnd_3364344 := by
    simpa [prefixWord, tailWord_3364344, baseEnd_3364344] using wordTrace_append hprefix tailTrace_3364344
  have hstable : (prefixWord ++ tailWord_3364344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364344).length < 2 ^ (prefixWord ++ tailWord_3364344).sum := by decide
  have hdescent : baseEnd_3364344 < baseStart_3364344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364350 : List Nat := [4, 2, 2, 3, 1, 2, 2, 1, 5]
def baseStart_3364350 : Nat := 118140960795 + 3364350 * 2 ^ 59
def prefixEnd_3364350 : Nat := 4983230072969 + 3 ^ 40 * 3364350 * 2
def baseEnd_3364350 : Nat := 383895253323114933078365

theorem tailTrace_3364350 : CollatzResearch.WordTrace tailWord_3364350 prefixEnd_3364350 383895253323114933078365 := by
  unfold tailWord_3364350
  simp only [CollatzResearch.WordTrace]
  refine ⟨15338490670192751260005313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81805283574361340053361669 15338490670192751260005313)
  ·
    refine ⟨11503868002644563445003985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15338490670192751260005313 11503868002644563445003985)
    ·
      refine ⟨8627901001983422583752989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11503868002644563445003985 8627901001983422583752989)
      ·
        refine ⟨3235462875743783468907371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8627901001983422583752989 3235462875743783468907371)
        ·
          refine ⟨4853194313615675203361057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3235462875743783468907371 4853194313615675203361057)
          ·
            refine ⟨3639895735211756402520793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4853194313615675203361057 3639895735211756402520793)
            ·
              refine ⟨2729921801408817301890595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3639895735211756402520793 2729921801408817301890595)
              ·
                refine ⟨4094882702113225952835893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2729921801408817301890595 4094882702113225952835893)
                ·
                  refine ⟨383895253323114933078365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4094882702113225952835893 383895253323114933078365)
                  ·
                    rfl

theorem cell22_3364350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_3364350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3364350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3364350 prefixEnd_3364350 := by exact prefixLift 3364350
  have htrace : WordTrace (prefixWord ++ tailWord_3364350) baseStart_3364350 baseEnd_3364350 := by
    simpa [prefixWord, tailWord_3364350, baseEnd_3364350] using wordTrace_append hprefix tailTrace_3364350
  have hstable : (prefixWord ++ tailWord_3364350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364350).length < 2 ^ (prefixWord ++ tailWord_3364350).sum := by decide
  have hdescent : baseEnd_3364350 < baseStart_3364350 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364357 : List Nat := [1, 3, 1, 1, 2, 2, 1, 1, 6, 4]
def baseStart_3364357 : Nat := 118140960795 + 3364357 * 2 ^ 59
def prefixEnd_3364357 : Nat := 4983230072969 + 3 ^ 40 * 3364357 * 2
def baseEnd_3364357 : Nat := 1151688156212399114310073

theorem tailTrace_3364357 : CollatzResearch.WordTrace tailWord_3364357 prefixEnd_3364357 1151688156212399114310073 := by
  unfold tailWord_3364357
  simp only [CollatzResearch.WordTrace]
  refine ⟨122708180672516650275547325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81805453781677766850364883 122708180672516650275547325)
  ·
    refine ⟨46015567752193743853330247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122708180672516650275547325 46015567752193743853330247)
    ·
      refine ⟨69023351628290615779995371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46015567752193743853330247 69023351628290615779995371)
      ·
        refine ⟨103535027442435923669993057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69023351628290615779995371 103535027442435923669993057)
        ·
          refine ⟨77651270581826942752494793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103535027442435923669993057 77651270581826942752494793)
          ·
            refine ⟨58238452936370207064371095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77651270581826942752494793 58238452936370207064371095)
            ·
              refine ⟨87357679404555310596556643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58238452936370207064371095 87357679404555310596556643)
              ·
                refine ⟨131036519106832965894834965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87357679404555310596556643 131036519106832965894834965)
                ·
                  refine ⟨6142336833132795276320389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 131036519106832965894834965 6142336833132795276320389)
                  ·
                    refine ⟨1151688156212399114310073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6142336833132795276320389 1151688156212399114310073)
                    ·
                      rfl

theorem cell22_3364357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 6, 4].length) (baseStart_3364357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3364357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3364357 prefixEnd_3364357 := by exact prefixLift 3364357
  have htrace : WordTrace (prefixWord ++ tailWord_3364357) baseStart_3364357 baseEnd_3364357 := by
    simpa [prefixWord, tailWord_3364357, baseEnd_3364357] using wordTrace_append hprefix tailTrace_3364357
  have hstable : (prefixWord ++ tailWord_3364357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364357).length < 2 ^ (prefixWord ++ tailWord_3364357).sum := by decide
  have hdescent : baseEnd_3364357 < baseStart_3364357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364363 : List Nat := [1, 1, 1, 1, 9, 1, 1, 2, 1, 4]
def baseStart_3364363 : Nat := 118140960795 + 3364363 * 2 ^ 59
def prefixEnd_3364363 : Nat := 4983230072969 + 3 ^ 40 * 3364363 * 2
def baseEnd_3364363 : Nat := 1151690210135017098660055

theorem tailTrace_3364363 : CollatzResearch.WordTrace tailWord_3364363 prefixEnd_3364363 1151690210135017098660055 := by
  unfold tailWord_3364363
  simp only [CollatzResearch.WordTrace]
  refine ⟨122708399510494913300265743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81805599673663275533510495 122708399510494913300265743)
  ·
    refine ⟨184062599265742369950398615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122708399510494913300265743 184062599265742369950398615)
    ·
      refine ⟨276093898898613554925597923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184062599265742369950398615 276093898898613554925597923)
      ·
        refine ⟨414140848347920332388396885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276093898898613554925597923 414140848347920332388396885)
        ·
          refine ⟨2426606533288595697588263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 414140848347920332388396885 2426606533288595697588263)
          ·
            refine ⟨3639909799932893546382395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2426606533288595697588263 3639909799932893546382395)
            ·
              refine ⟨5459864699899340319573593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3639909799932893546382395 5459864699899340319573593)
              ·
                refine ⟨4094898524924505239680195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5459864699899340319573593 4094898524924505239680195)
                ·
                  refine ⟨6142347787386757859520293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4094898524924505239680195 6142347787386757859520293)
                  ·
                    refine ⟨1151690210135017098660055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6142347787386757859520293 1151690210135017098660055)
                    ·
                      rfl

theorem cell22_3364363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 2, 1, 4].length) (baseStart_3364363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3364363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3364363 prefixEnd_3364363 := by exact prefixLift 3364363
  have htrace : WordTrace (prefixWord ++ tailWord_3364363) baseStart_3364363 baseEnd_3364363 := by
    simpa [prefixWord, tailWord_3364363, baseEnd_3364363] using wordTrace_append hprefix tailTrace_3364363
  have hstable : (prefixWord ++ tailWord_3364363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364363).length < 2 ^ (prefixWord ++ tailWord_3364363).sum := by decide
  have hdescent : baseEnd_3364363 < baseStart_3364363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364432 : List Nat := [2, 1, 1, 1, 1, 3, 3, 2, 1, 7]
def baseStart_3364432 : Nat := 118140960795 + 3364432 * 2 ^ 59
def prefixEnd_3364432 : Nat := 4983230072969 + 3 ^ 40 * 3364432 * 2
def baseEnd_3364432 : Nat := 1151713830245123918684843

theorem tailTrace_3364432 : CollatzResearch.WordTrace tailWord_3364432 prefixEnd_3364432 1151713830245123918684843 := by
  unfold tailWord_3364432
  simp only [CollatzResearch.WordTrace]
  refine ⟨61355458073622469042263775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81807277431496625389685033 61355458073622469042263775)
  ·
    refine ⟨92033187110433703563395663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61355458073622469042263775 92033187110433703563395663)
    ·
      refine ⟨138049780665650555345093495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92033187110433703563395663 138049780665650555345093495)
      ·
        refine ⟨207074670998475833017640243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138049780665650555345093495 207074670998475833017640243)
        ·
          refine ⟨310612006497713749526460365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207074670998475833017640243 310612006497713749526460365)
          ·
            refine ⟨116479502436642656072422637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 310612006497713749526460365 116479502436642656072422637)
            ·
              refine ⟨43679813413740996027158489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116479502436642656072422637 43679813413740996027158489)
              ·
                refine ⟨32759860060305747020368867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43679813413740996027158489 32759860060305747020368867)
                ·
                  refine ⟨49139790090458620530553301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32759860060305747020368867 49139790090458620530553301)
                  ·
                    refine ⟨1151713830245123918684843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49139790090458620530553301 1151713830245123918684843)
                    ·
                      rfl

theorem cell22_3364432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 1, 7].length) (baseStart_3364432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3364432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3364432 prefixEnd_3364432 := by exact prefixLift 3364432
  have htrace : WordTrace (prefixWord ++ tailWord_3364432) baseStart_3364432 baseEnd_3364432 := by
    simpa [prefixWord, tailWord_3364432, baseEnd_3364432] using wordTrace_append hprefix tailTrace_3364432
  have hstable : (prefixWord ++ tailWord_3364432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364432).length < 2 ^ (prefixWord ++ tailWord_3364432).sum := by decide
  have hdescent : baseEnd_3364432 < baseStart_3364432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364451 : List Nat := [1, 1, 1, 5, 1, 5, 1, 2, 5]
def baseStart_3364451 : Nat := 118140960795 + 3364451 * 2 ^ 59
def prefixEnd_3364451 : Nat := 4983230072969 + 3 ^ 40 * 3364451 * 2
def baseEnd_3364451 : Nat := 383906778111138067486595

theorem tailTrace_3364451 : CollatzResearch.WordTrace tailWord_3364451 prefixEnd_3364451 383906778111138067486595 := by
  unfold tailWord_3364451
  simp only [CollatzResearch.WordTrace]
  refine ⟨122711609134176104329469207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81807739422784069552979471 122711609134176104329469207)
  ·
    refine ⟨184067413701264156494203811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122711609134176104329469207 184067413701264156494203811)
    ·
      refine ⟨276101120551896234741305717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184067413701264156494203811 276101120551896234741305717)
      ·
        refine ⟨25884480051740272006997411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 276101120551896234741305717 25884480051740272006997411)
        ·
          refine ⟨38826720077610408010496117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25884480051740272006997411 38826720077610408010496117)
          ·
            refine ⟨3640005007275975750984011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38826720077610408010496117 3640005007275975750984011)
            ·
              refine ⟨5460007510913963626476017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3640005007275975750984011 5460007510913963626476017)
              ·
                refine ⟨4095005633185472719857013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5460007510913963626476017 4095005633185472719857013)
                ·
                  refine ⟨383906778111138067486595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4095005633185472719857013 383906778111138067486595)
                  ·
                    rfl

theorem cell22_3364451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 2, 5].length) (baseStart_3364451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3364451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3364451 prefixEnd_3364451 := by exact prefixLift 3364451
  have htrace : WordTrace (prefixWord ++ tailWord_3364451) baseStart_3364451 baseEnd_3364451 := by
    simpa [prefixWord, tailWord_3364451, baseEnd_3364451] using wordTrace_append hprefix tailTrace_3364451
  have hstable : (prefixWord ++ tailWord_3364451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364451).length < 2 ^ (prefixWord ++ tailWord_3364451).sum := by decide
  have hdescent : baseEnd_3364451 < baseStart_3364451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364481 : List Nat := [1, 2, 4, 2, 1, 2, 1, 4, 1, 4]
def baseStart_3364481 : Nat := 118140960795 + 3364481 * 2 ^ 59
def prefixEnd_3364481 : Nat := 4983230072969 + 3 ^ 40 * 3364481 * 2
def baseEnd_3364481 : Nat := 1151730603946504124209693

theorem tailTrace_3364481 : CollatzResearch.WordTrace tailWord_3364481 prefixEnd_3364481 1151730603946504124209693 := by
  unfold tailWord_3364481
  simp only [CollatzResearch.WordTrace]
  refine ⟨122712703324067419453061297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81808468882711612968707531 122712703324067419453061297)
  ·
    refine ⟨92034527493050564589795973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122712703324067419453061297 92034527493050564589795973)
    ·
      refine ⟨17256473904946980860586745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92034527493050564589795973 17256473904946980860586745)
      ·
        refine ⟨12942355428710235645440059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17256473904946980860586745 12942355428710235645440059)
        ·
          refine ⟨19413533143065353468160089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12942355428710235645440059 19413533143065353468160089)
          ·
            refine ⟨14560149857299015101120067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19413533143065353468160089 14560149857299015101120067)
            ·
              refine ⟨21840224785948522651680101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14560149857299015101120067 21840224785948522651680101)
              ·
                refine ⟨4095042147365347997190019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21840224785948522651680101 4095042147365347997190019)
                ·
                  refine ⟨6142563221048021995785029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4095042147365347997190019 6142563221048021995785029)
                  ·
                    refine ⟨1151730603946504124209693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6142563221048021995785029 1151730603946504124209693)
                    ·
                      rfl

theorem cell22_3364481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_3364481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3364481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3364481 prefixEnd_3364481 := by exact prefixLift 3364481
  have htrace : WordTrace (prefixWord ++ tailWord_3364481) baseStart_3364481 baseEnd_3364481 := by
    simpa [prefixWord, tailWord_3364481, baseEnd_3364481] using wordTrace_append hprefix tailTrace_3364481
  have hstable : (prefixWord ++ tailWord_3364481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364481).length < 2 ^ (prefixWord ++ tailWord_3364481).sum := by decide
  have hdescent : baseEnd_3364481 < baseStart_3364481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364528 : List Nat := [2, 1, 1, 1, 2, 1, 8, 1, 2, 3]
def baseStart_3364528 : Nat := 118140960795 + 3364528 * 2 ^ 59
def prefixEnd_3364528 : Nat := 4983230072969 + 3 ^ 40 * 3364528 * 2
def baseEnd_3364528 : Nat := 1151746693007011668284549

theorem tailTrace_3364528 : CollatzResearch.WordTrace tailWord_3364528 prefixEnd_3364528 1151746693007011668284549 := by
  unfold tailWord_3364528
  simp only [CollatzResearch.WordTrace]
  refine ⟨61357208777448573240011119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81809611703264764320014825 61357208777448573240011119)
  ·
    refine ⟨92035813166172859860016679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61357208777448573240011119 92035813166172859860016679)
    ·
      refine ⟨138053719749259289790025019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92035813166172859860016679 138053719749259289790025019)
      ·
        refine ⟨207080579623888934685037529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138053719749259289790025019 207080579623888934685037529)
        ·
          refine ⟨155310434717916701013778147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207080579623888934685037529 155310434717916701013778147)
          ·
            refine ⟨232965652076875051520667221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155310434717916701013778147 232965652076875051520667221)
            ·
              refine ⟨2730066235275879510007819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 232965652076875051520667221 2730066235275879510007819)
              ·
                refine ⟨4095099352913819265011729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2730066235275879510007819 4095099352913819265011729)
                ·
                  refine ⟨3071324514685364448758797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4095099352913819265011729 3071324514685364448758797)
                  ·
                    refine ⟨1151746693007011668284549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3071324514685364448758797 1151746693007011668284549)
                    ·
                      rfl

theorem cell22_3364528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8, 1, 2, 3].length) (baseStart_3364528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3364528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3364528 prefixEnd_3364528 := by exact prefixLift 3364528
  have htrace : WordTrace (prefixWord ++ tailWord_3364528) baseStart_3364528 baseEnd_3364528 := by
    simpa [prefixWord, tailWord_3364528, baseEnd_3364528] using wordTrace_append hprefix tailTrace_3364528
  have hstable : (prefixWord ++ tailWord_3364528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364528).length < 2 ^ (prefixWord ++ tailWord_3364528).sum := by decide
  have hdescent : baseEnd_3364528 < baseStart_3364528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364586 : List Nat := [3, 1, 3, 1, 1, 1, 4, 3, 5]
def baseStart_3364586 : Nat := 118140960795 + 3364586 * 2 ^ 59
def prefixEnd_3364586 : Nat := 4983230072969 + 3 ^ 40 * 3364586 * 2
def baseEnd_3364586 : Nat := 383922182530772950111457

theorem tailTrace_3364586 : CollatzResearch.WordTrace tailWord_3364586 prefixEnd_3364586 383922182530772950111457 := by
  unfold tailWord_3364586
  simp only [CollatzResearch.WordTrace]
  refine ⟨30679133247171755596408403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81811021992458014923755741 30679133247171755596408403)
  ·
    refine ⟨46018699870757633394612605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30679133247171755596408403 46018699870757633394612605)
    ·
      refine ⟨17257012451534112522979727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46018699870757633394612605 17257012451534112522979727)
      ·
        refine ⟨25885518677301168784469591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17257012451534112522979727 25885518677301168784469591)
        ·
          refine ⟨38828278015951753176704387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25885518677301168784469591 38828278015951753176704387)
          ·
            refine ⟨58242417023927629765056581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38828278015951753176704387 58242417023927629765056581)
            ·
              refine ⟨10920453191986430580948109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58242417023927629765056581 10920453191986430580948109)
              ·
                refine ⟨4095169946994911467855541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10920453191986430580948109 4095169946994911467855541)
                ·
                  refine ⟨383922182530772950111457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4095169946994911467855541 383922182530772950111457)
                  ·
                    rfl

theorem cell22_3364586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 3, 5].length) (baseStart_3364586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3364586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3364586 prefixEnd_3364586 := by exact prefixLift 3364586
  have htrace : WordTrace (prefixWord ++ tailWord_3364586) baseStart_3364586 baseEnd_3364586 := by
    simpa [prefixWord, tailWord_3364586, baseEnd_3364586] using wordTrace_append hprefix tailTrace_3364586
  have hstable : (prefixWord ++ tailWord_3364586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364586).length < 2 ^ (prefixWord ++ tailWord_3364586).sum := by decide
  have hdescent : baseEnd_3364586 < baseStart_3364586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364631 : List Nat := [1, 1, 3, 4, 2, 1, 1, 3, 6]
def baseStart_3364631 : Nat := 118140960795 + 3364631 * 2 ^ 59
def prefixEnd_3364631 : Nat := 4983230072969 + 3 ^ 40 * 3364631 * 2
def baseEnd_3364631 : Nat := 383927317337317910986411

theorem tailTrace_3364631 : CollatzResearch.WordTrace tailWord_3364631 prefixEnd_3364631 383927317337317910986411 := by
  unfold tailWord_3364631
  simp only [CollatzResearch.WordTrace]
  refine ⟨122718174273523995071021747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81812116182349330047347831 122718174273523995071021747)
  ·
    refine ⟨184077261410285992606532621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122718174273523995071021747 184077261410285992606532621)
    ·
      refine ⟨69028973028857247227449733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184077261410285992606532621 69028973028857247227449733)
      ·
        refine ⟨12942932442910733855146825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69028973028857247227449733 12942932442910733855146825)
        ·
          refine ⟨9707199332183050391360119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12942932442910733855146825 9707199332183050391360119)
          ·
            refine ⟨14560798998274575587040179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9707199332183050391360119 14560798998274575587040179)
            ·
              refine ⟨21841198497411863380560269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14560798998274575587040179 21841198497411863380560269)
              ·
                refine ⟨8190449436529448767710101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21841198497411863380560269 8190449436529448767710101)
                ·
                  refine ⟨383927317337317910986411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8190449436529448767710101 383927317337317910986411)
                  ·
                    rfl

theorem cell22_3364631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 3, 6].length) (baseStart_3364631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3364631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3364631 prefixEnd_3364631 := by exact prefixLift 3364631
  have htrace : WordTrace (prefixWord ++ tailWord_3364631) baseStart_3364631 baseEnd_3364631 := by
    simpa [prefixWord, tailWord_3364631, baseEnd_3364631] using wordTrace_append hprefix tailTrace_3364631
  have hstable : (prefixWord ++ tailWord_3364631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364631).length < 2 ^ (prefixWord ++ tailWord_3364631).sum := by decide
  have hdescent : baseEnd_3364631 < baseStart_3364631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364736 : List Nat := [2, 1, 1, 2, 1, 2, 4, 2, 2, 5]
def baseStart_3364736 : Nat := 118140960795 + 3364736 * 2 ^ 59
def prefixEnd_3364736 : Nat := 4983230072969 + 3 ^ 40 * 3364736 * 2
def baseEnd_3364736 : Nat := 1151817895657768459083911

theorem tailTrace_3364736 : CollatzResearch.WordTrace tailWord_3364736 prefixEnd_3364736 1151817895657768459083911 := by
  unfold tailWord_3364736
  simp only [CollatzResearch.WordTrace]
  refine ⟨61361001969071799001797031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81814669292095732002396041 61361001969071799001797031)
  ·
    refine ⟨92041502953607698502695547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61361001969071799001797031 92041502953607698502695547)
    ·
      refine ⟨138062254430411547754043321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92041502953607698502695547 138062254430411547754043321)
      ·
        refine ⟨103546690822808660815532491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138062254430411547754043321 103546690822808660815532491)
        ·
          refine ⟨155320036234212991223298737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103546690822808660815532491 155320036234212991223298737)
          ·
            refine ⟨116490027175659743417474053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155320036234212991223298737 116490027175659743417474053)
            ·
              refine ⟨21841880095436201890776385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116490027175659743417474053 21841880095436201890776385)
              ·
                refine ⟨16381410071577151418082289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21841880095436201890776385 16381410071577151418082289)
                ·
                  refine ⟨12286057553682863563561717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16381410071577151418082289 12286057553682863563561717)
                  ·
                    refine ⟨1151817895657768459083911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12286057553682863563561717 1151817895657768459083911)
                    ·
                      rfl

theorem cell22_3364736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 2, 5].length) (baseStart_3364736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3364736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3364736 prefixEnd_3364736 := by exact prefixLift 3364736
  have htrace : WordTrace (prefixWord ++ tailWord_3364736) baseStart_3364736 baseEnd_3364736 := by
    simpa [prefixWord, tailWord_3364736, baseEnd_3364736] using wordTrace_append hprefix tailTrace_3364736
  have hstable : (prefixWord ++ tailWord_3364736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364736).length < 2 ^ (prefixWord ++ tailWord_3364736).sum := by decide
  have hdescent : baseEnd_3364736 < baseStart_3364736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364768 : List Nat := [2, 1, 1, 4, 1, 1, 1, 6, 1, 4]
def baseStart_3364768 : Nat := 118140960795 + 3364768 * 2 ^ 59
def prefixEnd_3364768 : Nat := 4983230072969 + 3 ^ 40 * 3364768 * 2
def baseEnd_3364768 : Nat := 1151828849911731042283813

theorem tailTrace_3364768 : CollatzResearch.WordTrace tailWord_3364768 prefixEnd_3364768 1151828849911731042283813 := by
  unfold tailWord_3364768
  simp only [CollatzResearch.WordTrace]
  refine ⟨61361585537013833734379479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81815447382685111645839305 61361585537013833734379479)
  ·
    refine ⟨92042378305520750601569219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61361585537013833734379479 92042378305520750601569219)
    ·
      refine ⟨138063567458281125902353829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92042378305520750601569219 138063567458281125902353829)
      ·
        refine ⟨25886918898427711106691343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138063567458281125902353829 25886918898427711106691343)
        ·
          refine ⟨38830378347641566660037015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25886918898427711106691343 38830378347641566660037015)
          ·
            refine ⟨58245567521462349990055523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38830378347641566660037015 58245567521462349990055523)
            ·
              refine ⟨87368351282193524985083285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58245567521462349990055523 87368351282193524985083285)
              ·
                refine ⟨4095391466352821483675779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 87368351282193524985083285 4095391466352821483675779)
                ·
                  refine ⟨6143087199529232225513669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4095391466352821483675779 6143087199529232225513669)
                  ·
                    refine ⟨1151828849911731042283813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6143087199529232225513669 1151828849911731042283813)
                    ·
                      rfl

theorem cell22_3364768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 6, 1, 4].length) (baseStart_3364768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3364768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3364768 prefixEnd_3364768 := by exact prefixLift 3364768
  have htrace : WordTrace (prefixWord ++ tailWord_3364768) baseStart_3364768 baseEnd_3364768 := by
    simpa [prefixWord, tailWord_3364768, baseEnd_3364768] using wordTrace_append hprefix tailTrace_3364768
  have hstable : (prefixWord ++ tailWord_3364768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364768).length < 2 ^ (prefixWord ++ tailWord_3364768).sum := by decide
  have hdescent : baseEnd_3364768 < baseStart_3364768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364776 : List Nat := [2, 1, 6, 2, 1, 1, 2, 3, 1, 3]
def baseStart_3364776 : Nat := 118140960795 + 3364776 * 2 ^ 59
def prefixEnd_3364776 : Nat := 4983230072969 + 3 ^ 40 * 3364776 * 2
def baseEnd_3364776 : Nat := 1151831588475221688083789

theorem tailTrace_3364776 : CollatzResearch.WordTrace tailWord_3364776 prefixEnd_3364776 1151831588475221688083789 := by
  unfold tailWord_3364776
  simp only [CollatzResearch.WordTrace]
  refine ⟨61361731428999342417525091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81815641905332456556700121 61361731428999342417525091)
  ·
    refine ⟨92042597143499013626287637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61361731428999342417525091 92042597143499013626287637)
    ·
      refine ⟨4314496741101516263732233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 92042597143499013626287637 4314496741101516263732233)
      ·
        refine ⟨3235872555826137197799175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4314496741101516263732233 3235872555826137197799175)
        ·
          refine ⟨4853808833739205796698763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3235872555826137197799175 4853808833739205796698763)
          ·
            refine ⟨7280713250608808695048145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4853808833739205796698763 7280713250608808695048145)
            ·
              refine ⟨5460534937956606521286109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7280713250608808695048145 5460534937956606521286109)
              ·
                refine ⟨2047700601733727445482291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5460534937956606521286109 2047700601733727445482291)
                ·
                  refine ⟨3071550902600591168223437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2047700601733727445482291 3071550902600591168223437)
                  ·
                    refine ⟨1151831588475221688083789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3071550902600591168223437 1151831588475221688083789)
                    ·
                      rfl

theorem cell22_3364776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_3364776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3364776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3364776 prefixEnd_3364776 := by exact prefixLift 3364776
  have htrace : WordTrace (prefixWord ++ tailWord_3364776) baseStart_3364776 baseEnd_3364776 := by
    simpa [prefixWord, tailWord_3364776, baseEnd_3364776] using wordTrace_append hprefix tailTrace_3364776
  have hstable : (prefixWord ++ tailWord_3364776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364776).length < 2 ^ (prefixWord ++ tailWord_3364776).sum := by decide
  have hdescent : baseEnd_3364776 < baseStart_3364776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364785 : List Nat := [1, 2, 2, 4, 2, 2, 1, 3, 1, 4]
def baseStart_3364785 : Nat := 118140960795 + 3364785 * 2 ^ 59
def prefixEnd_3364785 : Nat := 4983230072969 + 3 ^ 40 * 3364785 * 2
def baseEnd_3364785 : Nat := 1151834669359148664608761

theorem tailTrace_3364785 : CollatzResearch.WordTrace tailWord_3364785 prefixEnd_3364785 1151834669359148664608761 := by
  unfold tailWord_3364785
  simp only [CollatzResearch.WordTrace]
  refine ⟨122723791114966079372127809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81815860743310719581418539 122723791114966079372127809)
  ·
    refine ⟨92042843336224559529095857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122723791114966079372127809 92042843336224559529095857)
    ·
      refine ⟨69032132502168419646821893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92042843336224559529095857 69032132502168419646821893)
      ·
        refine ⟨12943524844156578683779105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69032132502168419646821893 12943524844156578683779105)
        ·
          refine ⟨9707643633117434012834329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12943524844156578683779105 9707643633117434012834329)
          ·
            refine ⟨7280732724838075509625747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9707643633117434012834329 7280732724838075509625747)
            ·
              refine ⟨10921099087257113264438621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7280732724838075509625747 10921099087257113264438621)
              ·
                refine ⟨4095412157721417474164483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10921099087257113264438621 4095412157721417474164483)
                ·
                  refine ⟨6143118236582126211246725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4095412157721417474164483 6143118236582126211246725)
                  ·
                    refine ⟨1151834669359148664608761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6143118236582126211246725 1151834669359148664608761)
                    ·
                      rfl

theorem cell22_3364785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 3, 1, 4].length) (baseStart_3364785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3364785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3364785 prefixEnd_3364785 := by exact prefixLift 3364785
  have htrace : WordTrace (prefixWord ++ tailWord_3364785) baseStart_3364785 baseEnd_3364785 := by
    simpa [prefixWord, tailWord_3364785, baseEnd_3364785] using wordTrace_append hprefix tailTrace_3364785
  have hstable : (prefixWord ++ tailWord_3364785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364785).length < 2 ^ (prefixWord ++ tailWord_3364785).sum := by decide
  have hdescent : baseEnd_3364785 < baseStart_3364785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364811 : List Nat := [1, 1, 1, 1, 3, 4, 2, 9]
def baseStart_3364811 : Nat := 118140960795 + 3364811 * 2 ^ 59
def prefixEnd_3364811 : Nat := 4983230072969 + 3 ^ 40 * 3364811 * 2
def baseEnd_3364811 : Nat := 127982618854499251495409

theorem tailTrace_3364811 : CollatzResearch.WordTrace tailWord_3364811 prefixEnd_3364811 127982618854499251495409 := by
  unfold tailWord_3364811
  simp only [CollatzResearch.WordTrace]
  refine ⟨122724739412871885812574287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81816492941914590541716191 122724739412871885812574287)
  ·
    refine ⟨184087109119307828718861431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122724739412871885812574287 184087109119307828718861431)
    ·
      refine ⟨276130663678961743078292147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184087109119307828718861431 276130663678961743078292147)
      ·
        refine ⟨414195995518442614617438221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276130663678961743078292147 414195995518442614617438221)
        ·
          refine ⟨155323498319415980481539333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 414195995518442614617438221 155323498319415980481539333)
          ·
            refine ⟨29123155934890496340288625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155323498319415980481539333 29123155934890496340288625)
            ·
              refine ⟨21842366951167872255216469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29123155934890496340288625 21842366951167872255216469)
              ·
                refine ⟨127982618854499251495409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21842366951167872255216469 127982618854499251495409)
                ·
                  rfl

theorem cell22_3364811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 9].length) (baseStart_3364811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3364811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3364811 prefixEnd_3364811 := by exact prefixLift 3364811
  have htrace : WordTrace (prefixWord ++ tailWord_3364811) baseStart_3364811 baseEnd_3364811 := by
    simpa [prefixWord, tailWord_3364811, baseEnd_3364811] using wordTrace_append hprefix tailTrace_3364811
  have hstable : (prefixWord ++ tailWord_3364811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364811).length < 2 ^ (prefixWord ++ tailWord_3364811).sum := by decide
  have hdescent : baseEnd_3364811 < baseStart_3364811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364843 : List Nat := [1, 1, 1, 1, 2, 3, 1, 4, 5, 3]
def baseStart_3364843 : Nat := 118140960795 + 3364843 * 2 ^ 59
def prefixEnd_3364843 : Nat := 4983230072969 + 3 ^ 40 * 3364843 * 2
def baseEnd_3364843 : Nat := 1151854523944455846658583

theorem tailTrace_3364843 : CollatzResearch.WordTrace tailWord_3364843 prefixEnd_3364843 1151854523944455846658583 := by
  unfold tailWord_3364843
  simp only [CollatzResearch.WordTrace]
  refine ⟨122725906548755955277739183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81817271032503970185159455 122725906548755955277739183)
  ·
    refine ⟨184088859823133932916608775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122725906548755955277739183 184088859823133932916608775)
    ·
      refine ⟨276133289734700899374913163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184088859823133932916608775 276133289734700899374913163)
      ·
        refine ⟨414199934602051349062369745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276133289734700899374913163 414199934602051349062369745)
        ·
          refine ⟨310649950951538511796777309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 414199934602051349062369745 310649950951538511796777309)
          ·
            refine ⟨116493731606826941923791491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 310649950951538511796777309 116493731606826941923791491)
            ·
              refine ⟨174740597410240412885687237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116493731606826941923791491 174740597410240412885687237)
              ·
                refine ⟨32763862014420077416066357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 174740597410240412885687237 32763862014420077416066357)
                ·
                  refine ⟨3071612063851882257756221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32763862014420077416066357 3071612063851882257756221)
                  ·
                    refine ⟨1151854523944455846658583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3071612063851882257756221 1151854523944455846658583)
                    ·
                      rfl

theorem cell22_3364843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 5, 3].length) (baseStart_3364843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3364843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3364843 prefixEnd_3364843 := by exact prefixLift 3364843
  have htrace : WordTrace (prefixWord ++ tailWord_3364843) baseStart_3364843 baseEnd_3364843 := by
    simpa [prefixWord, tailWord_3364843, baseEnd_3364843] using wordTrace_append hprefix tailTrace_3364843
  have hstable : (prefixWord ++ tailWord_3364843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364843).length < 2 ^ (prefixWord ++ tailWord_3364843).sum := by decide
  have hdescent : baseEnd_3364843 < baseStart_3364843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364870 : List Nat := [6, 2, 1, 2, 2, 1, 1, 2, 1, 4]
def baseStart_3364870 : Nat := 118140960795 + 3364870 * 2 ^ 59
def prefixEnd_3364870 : Nat := 4983230072969 + 3 ^ 40 * 3364870 * 2
def baseEnd_3364870 : Nat := 1151863766596236776233501

theorem tailTrace_3364870 : CollatzResearch.WordTrace tailWord_3364870 prefixEnd_3364870 1151863766596236776233501 := by
  unfold tailWord_3364870
  simp only [CollatzResearch.WordTrace]
  refine ⟨3835215353739316840280377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 81817927546438759259314709 3835215353739316840280377)
  ·
    refine ⟨2876411515304487630210283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3835215353739316840280377 2876411515304487630210283)
    ·
      refine ⟨4314617272956731445315425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2876411515304487630210283 4314617272956731445315425)
      ·
        refine ⟨3235962954717548583986569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4314617272956731445315425 3235962954717548583986569)
        ·
          refine ⟨2426972216038161437989927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3235962954717548583986569 2426972216038161437989927)
          ·
            refine ⟨3640458324057242156984891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2426972216038161437989927 3640458324057242156984891)
            ·
              refine ⟨5460687486085863235477337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3640458324057242156984891 5460687486085863235477337)
              ·
                refine ⟨4095515614564397426608003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5460687486085863235477337 4095515614564397426608003)
                ·
                  refine ⟨6143273421846596139912005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4095515614564397426608003 6143273421846596139912005)
                  ·
                    refine ⟨1151863766596236776233501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6143273421846596139912005 1151863766596236776233501)
                    ·
                      rfl

theorem cell22_3364870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_3364870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3364870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3364870 prefixEnd_3364870 := by exact prefixLift 3364870
  have htrace : WordTrace (prefixWord ++ tailWord_3364870) baseStart_3364870 baseEnd_3364870 := by
    simpa [prefixWord, tailWord_3364870, baseEnd_3364870] using wordTrace_append hprefix tailTrace_3364870
  have hstable : (prefixWord ++ tailWord_3364870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364870).length < 2 ^ (prefixWord ++ tailWord_3364870).sum := by decide
  have hdescent : baseEnd_3364870 < baseStart_3364870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364952 : List Nat := [2, 1, 2, 2, 1, 5, 2, 3, 4]
def baseStart_3364952 : Nat := 118140960795 + 3364952 * 2 ^ 59
def prefixEnd_3364952 : Nat := 4983230072969 + 3 ^ 40 * 3364952 * 2
def baseEnd_3364952 : Nat := 383963945624005298561083

theorem tailTrace_3364952 : CollatzResearch.WordTrace tailWord_3364952 prefixEnd_3364952 383963945624005298561083 := by
  unfold tailWord_3364952
  simp only [CollatzResearch.WordTrace]
  refine ⟨61364941052680533446728555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81819921403574044595638073 61364941052680533446728555)
  ·
    refine ⟨92047411579020800170092833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61364941052680533446728555 92047411579020800170092833)
    ·
      refine ⟨69035558684265600127569625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92047411579020800170092833 69035558684265600127569625)
      ·
        refine ⟨51776669013199200095677219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69035558684265600127569625 51776669013199200095677219)
        ·
          refine ⟨77665003519798800143515829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51776669013199200095677219 77665003519798800143515829)
          ·
            refine ⟨7281094079981137513454609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77665003519798800143515829 7281094079981137513454609)
            ·
              refine ⟨5460820559985853135090957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7281094079981137513454609 5460820559985853135090957)
              ·
                refine ⟨2047807709994694925659109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5460820559985853135090957 2047807709994694925659109)
                ·
                  refine ⟨383963945624005298561083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2047807709994694925659109 383963945624005298561083)
                  ·
                    rfl

theorem cell22_3364952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 3, 4].length) (baseStart_3364952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3364952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3364952 prefixEnd_3364952 := by exact prefixLift 3364952
  have htrace : WordTrace (prefixWord ++ tailWord_3364952) baseStart_3364952 baseEnd_3364952 := by
    simpa [prefixWord, tailWord_3364952, baseEnd_3364952] using wordTrace_append hprefix tailTrace_3364952
  have hstable : (prefixWord ++ tailWord_3364952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364952).length < 2 ^ (prefixWord ++ tailWord_3364952).sum := by decide
  have hdescent : baseEnd_3364952 < baseStart_3364952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364958 : List Nat := [4, 4, 1, 1, 3, 1, 1, 2, 5]
def baseStart_3364958 : Nat := 118140960795 + 3364958 * 2 ^ 59
def prefixEnd_3364958 : Nat := 4983230072969 + 3 ^ 40 * 3364958 * 2
def baseEnd_3364958 : Nat := 383964630264877960011077

theorem tailTrace_3364958 : CollatzResearch.WordTrace tailWord_3364958 prefixEnd_3364958 383964630264877960011077 := by
  unfold tailWord_3364958
  simp only [CollatzResearch.WordTrace]
  refine ⟨15341262617917416239771941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81820067295559553278783685 15341262617917416239771941)
  ·
    refine ⟨2876486740859515544957239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15341262617917416239771941 2876486740859515544957239)
    ·
      refine ⟨4314730111289273317435859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2876486740859515544957239 4314730111289273317435859)
      ·
        refine ⟨6472095166933909976153789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4314730111289273317435859 6472095166933909976153789)
        ·
          refine ⟨2427035687600216241057671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6472095166933909976153789 2427035687600216241057671)
          ·
            refine ⟨3640553531400324361586507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2427035687600216241057671 3640553531400324361586507)
            ·
              refine ⟨5460830297100486542379761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3640553531400324361586507 5460830297100486542379761)
              ·
                refine ⟨4095622722825364906784821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5460830297100486542379761 4095622722825364906784821)
                ·
                  refine ⟨383964630264877960011077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4095622722825364906784821 383964630264877960011077)
                  ·
                    rfl

theorem cell22_3364958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_3364958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3364958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3364958 prefixEnd_3364958 := by exact prefixLift 3364958
  have htrace : WordTrace (prefixWord ++ tailWord_3364958) baseStart_3364958 baseEnd_3364958 := by
    simpa [prefixWord, tailWord_3364958, baseEnd_3364958] using wordTrace_append hprefix tailTrace_3364958
  have hstable : (prefixWord ++ tailWord_3364958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364958).length < 2 ^ (prefixWord ++ tailWord_3364958).sum := by decide
  have hdescent : baseEnd_3364958 < baseStart_3364958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364997 : List Nat := [1, 3, 1, 1, 5, 3, 2, 6]
def baseStart_3364997 : Nat := 118140960795 + 3364997 * 2 ^ 59
def prefixEnd_3364997 : Nat := 4983230072969 + 3 ^ 40 * 3364997 * 2
def baseEnd_3364997 : Nat := 127989693476850086478679

theorem tailTrace_3364997 : CollatzResearch.WordTrace tailWord_3364997 prefixEnd_3364997 127989693476850086478679 := by
  unfold tailWord_3364997
  simp only [CollatzResearch.WordTrace]
  refine ⟨122731523390198039578845245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81821015593465359719230163 122731523390198039578845245)
  ·
    refine ⟨46024321271324264842066967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122731523390198039578845245 46024321271324264842066967)
    ·
      refine ⟨69036481906986397263100451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46024321271324264842066967 69036481906986397263100451)
      ·
        refine ⟨103554722860479595894650677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69036481906986397263100451 103554722860479595894650677)
        ·
          refine ⟨9708255268169962115123501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 103554722860479595894650677 9708255268169962115123501)
          ·
            refine ⟨3640595725563735793171313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9708255268169962115123501 3640595725563735793171313)
            ·
              refine ⟨2730446794172801844878485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3640595725563735793171313 2730446794172801844878485)
              ·
                refine ⟨127989693476850086478679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2730446794172801844878485 127989693476850086478679)
                ·
                  rfl

theorem cell22_3364997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2, 6].length) (baseStart_3364997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3364997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3364997 prefixEnd_3364997 := by exact prefixLift 3364997
  have htrace : WordTrace (prefixWord ++ tailWord_3364997) baseStart_3364997 baseEnd_3364997 := by
    simpa [prefixWord, tailWord_3364997, baseEnd_3364997] using wordTrace_append hprefix tailTrace_3364997
  have hstable : (prefixWord ++ tailWord_3364997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364997).length < 2 ^ (prefixWord ++ tailWord_3364997).sum := by decide
  have hdescent : baseEnd_3364997 < baseStart_3364997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365008 : List Nat := [2, 1, 1, 1, 1, 1, 5, 1, 9]
def baseStart_3365008 : Nat := 118140960795 + 3365008 * 2 ^ 59
def prefixEnd_3365008 : Nat := 4983230072969 + 3 ^ 40 * 3365008 * 2
def baseEnd_3365008 : Nat := 383970335605483472094359

theorem tailTrace_3365008 : CollatzResearch.WordTrace tailWord_3365008 prefixEnd_3365008 383970335605483472094359 := by
  unfold tailWord_3365008
  simp only [CollatzResearch.WordTrace]
  refine ⟨61365962296579094228747839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81821283062105458971663785 61365962296579094228747839)
  ·
    refine ⟨92048943444868641343121759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61365962296579094228747839 92048943444868641343121759)
    ·
      refine ⟨138073415167302962014682639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92048943444868641343121759 138073415167302962014682639)
      ·
        refine ⟨207110122750954443022023959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138073415167302962014682639 207110122750954443022023959)
        ·
          refine ⟨310665184126431664533035939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207110122750954443022023959 310665184126431664533035939)
          ·
            refine ⟨465997776189647496799553909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310665184126431664533035939 465997776189647496799553909)
            ·
              refine ⟨43687291517779452824958179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 465997776189647496799553909 43687291517779452824958179)
              ·
                refine ⟨65530937276669179237437269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43687291517779452824958179 65530937276669179237437269)
                ·
                  refine ⟨383970335605483472094359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 65530937276669179237437269 383970335605483472094359)
                  ·
                    rfl

theorem cell22_3365008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 9].length) (baseStart_3365008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3365008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3365008 prefixEnd_3365008 := by exact prefixLift 3365008
  have htrace : WordTrace (prefixWord ++ tailWord_3365008) baseStart_3365008 baseEnd_3365008 := by
    simpa [prefixWord, tailWord_3365008, baseEnd_3365008] using wordTrace_append hprefix tailTrace_3365008
  have hstable : (prefixWord ++ tailWord_3365008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365008).length < 2 ^ (prefixWord ++ tailWord_3365008).sum := by decide
  have hdescent : baseEnd_3365008 < baseStart_3365008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365025 : List Nat := [1, 2, 3, 3, 1, 2, 2, 1, 7]
def baseStart_3365025 : Nat := 118140960795 + 3365025 * 2 ^ 59
def prefixEnd_3365025 : Nat := 4983230072969 + 3 ^ 40 * 3365025 * 2
def baseEnd_3365025 : Nat := 383972275421289346202675

theorem tailTrace_3365025 : CollatzResearch.WordTrace tailWord_3365025 prefixEnd_3365025 383972275421289346202675 := by
  unfold tailWord_3365025
  simp only [CollatzResearch.WordTrace]
  refine ⟨122732544634096600360864529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81821696422731066907243019 122732544634096600360864529)
  ·
    refine ⟨92049408475572450270648397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122732544634096600360864529 92049408475572450270648397)
    ·
      refine ⟨34518528178339668851493149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92049408475572450270648397 34518528178339668851493149)
      ·
        refine ⟨12944448066877375819309931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34518528178339668851493149 12944448066877375819309931)
        ·
          refine ⟨19416672100316063728964897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12944448066877375819309931 19416672100316063728964897)
          ·
            refine ⟨14562504075237047796723673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19416672100316063728964897 14562504075237047796723673)
            ·
              refine ⟨10921878056427785847542755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14562504075237047796723673 10921878056427785847542755)
              ·
                refine ⟨16382817084641678771314133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10921878056427785847542755 16382817084641678771314133)
                ·
                  refine ⟨383972275421289346202675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16382817084641678771314133 383972275421289346202675)
                  ·
                    rfl

theorem cell22_3365025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 7].length) (baseStart_3365025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3365025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3365025 prefixEnd_3365025 := by exact prefixLift 3365025
  have htrace : WordTrace (prefixWord ++ tailWord_3365025) baseStart_3365025 baseEnd_3365025 := by
    simpa [prefixWord, tailWord_3365025, baseEnd_3365025] using wordTrace_append hprefix tailTrace_3365025
  have hstable : (prefixWord ++ tailWord_3365025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365025).length < 2 ^ (prefixWord ++ tailWord_3365025).sum := by decide
  have hdescent : baseEnd_3365025 < baseStart_3365025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365100 : List Nat := [2, 2, 1, 1, 2, 3, 2, 2, 1, 6]
def baseStart_3365100 : Nat := 118140960795 + 3365100 * 2 ^ 59
def prefixEnd_3365100 : Nat := 4983230072969 + 3 ^ 40 * 3365100 * 2
def baseEnd_3365100 : Nat := 1151942500296592842982795

theorem tailTrace_3365100 : CollatzResearch.WordTrace tailWord_3365100 prefixEnd_3365100 1151942500296592842982795 := by
  unfold tailWord_3365100
  simp only [CollatzResearch.WordTrace]
  refine ⟨61367640054412444084922377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81823520072549925446563169 61367640054412444084922377)
  ·
    refine ⟨46025730040809333063691783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61367640054412444084922377 46025730040809333063691783)
    ·
      refine ⟨69038595061213999595537675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46025730040809333063691783 69038595061213999595537675)
      ·
        refine ⟨103557892591820999393306513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69038595061213999595537675 103557892591820999393306513)
        ·
          refine ⟨77668419443865749544979885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103557892591820999393306513 77668419443865749544979885)
          ·
            refine ⟨29125657291449656079367457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77668419443865749544979885 29125657291449656079367457)
            ·
              refine ⟨21844242968587242059525593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29125657291449656079367457 21844242968587242059525593)
              ·
                refine ⟨16383182226440431544644195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21844242968587242059525593 16383182226440431544644195)
                ·
                  refine ⟨24574773339660647316966293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16383182226440431544644195 24574773339660647316966293)
                  ·
                    refine ⟨1151942500296592842982795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24574773339660647316966293 1151942500296592842982795)
                    ·
                      rfl

theorem cell22_3365100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 6].length) (baseStart_3365100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3365100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3365100 prefixEnd_3365100 := by exact prefixLift 3365100
  have htrace : WordTrace (prefixWord ++ tailWord_3365100) baseStart_3365100 baseEnd_3365100 := by
    simpa [prefixWord, tailWord_3365100, baseEnd_3365100] using wordTrace_append hprefix tailTrace_3365100
  have hstable : (prefixWord ++ tailWord_3365100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365100).length < 2 ^ (prefixWord ++ tailWord_3365100).sum := by decide
  have hdescent : baseEnd_3365100 < baseStart_3365100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365102 : List Nat := [4, 1, 2, 1, 1, 1, 1, 2, 6, 3]
def baseStart_3365102 : Nat := 118140960795 + 3365102 * 2 ^ 59
def prefixEnd_3365102 : Nat := 4983230072969 + 3 ^ 40 * 3365102 * 2
def baseEnd_3365102 : Nat := 1151943184937465504432789

theorem tailTrace_3365102 : CollatzResearch.WordTrace tailWord_3365102 prefixEnd_3365102 1151943184937465504432789 := by
  unfold tailWord_3365102
  simp only [CollatzResearch.WordTrace]
  refine ⟨15341919131852205313927195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81823568703211761674278373 15341919131852205313927195)
  ·
    refine ⟨23012878697778307970890793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15341919131852205313927195 23012878697778307970890793)
    ·
      refine ⟨17259659023333730978168095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23012878697778307970890793 17259659023333730978168095)
      ·
        refine ⟨25889488535000596467252143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17259659023333730978168095 25889488535000596467252143)
        ·
          refine ⟨38834232802500894700878215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25889488535000596467252143 38834232802500894700878215)
          ·
            refine ⟨58251349203751342051317323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38834232802500894700878215 58251349203751342051317323)
            ·
              refine ⟨87377023805627013076975985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58251349203751342051317323 87377023805627013076975985)
              ·
                refine ⟨65532767854220259807731989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87377023805627013076975985 65532767854220259807731989)
                ·
                  refine ⟨3071848493166574678487437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 65532767854220259807731989 3071848493166574678487437)
                  ·
                    refine ⟨1151943184937465504432789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3071848493166574678487437 1151943184937465504432789)
                    ·
                      rfl

theorem cell22_3365102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_3365102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3365102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3365102 prefixEnd_3365102 := by exact prefixLift 3365102
  have htrace : WordTrace (prefixWord ++ tailWord_3365102) baseStart_3365102 baseEnd_3365102 := by
    simpa [prefixWord, tailWord_3365102, baseEnd_3365102] using wordTrace_append hprefix tailTrace_3365102
  have hstable : (prefixWord ++ tailWord_3365102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365102).length < 2 ^ (prefixWord ++ tailWord_3365102).sum := by decide
  have hdescent : baseEnd_3365102 < baseStart_3365102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365147 : List Nat := [1, 1, 1, 1, 1, 1, 7, 3, 3, 3]
def baseStart_3365147 : Nat := 118140960795 + 3365147 * 2 ^ 59
def prefixEnd_3365147 : Nat := 4983230072969 + 3 ^ 40 * 3365147 * 2
def baseEnd_3365147 : Nat := 1151958589357100387057651

theorem tailTrace_3365147 : CollatzResearch.WordTrace tailWord_3365147 prefixEnd_3365147 1151958589357100387057651 := by
  unfold tailWord_3365147
  simp only [CollatzResearch.WordTrace]
  refine ⟨122736994339654615196805695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81824662893103076797870463 122736994339654615196805695)
  ·
    refine ⟨184105491509481922795208543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122736994339654615196805695 184105491509481922795208543)
    ·
      refine ⟨276158237264222884192812815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184105491509481922795208543 276158237264222884192812815)
      ·
        refine ⟨414237355896334326289219223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276158237264222884192812815 414237355896334326289219223)
        ·
          refine ⟨621356033844501489433828835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414237355896334326289219223 621356033844501489433828835)
          ·
            refine ⟨932034050766752234150743253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 621356033844501489433828835 932034050766752234150743253)
            ·
              refine ⟨21844548064845755487908045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 932034050766752234150743253 21844548064845755487908045)
              ·
                refine ⟨8191705524317158307965517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21844548064845755487908045 8191705524317158307965517)
                ·
                  refine ⟨3071889571618934365487069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8191705524317158307965517 3071889571618934365487069)
                  ·
                    refine ⟨1151958589357100387057651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3071889571618934365487069 1151958589357100387057651)
                    ·
                      rfl

theorem cell22_3365147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3, 3, 3].length) (baseStart_3365147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3365147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3365147 prefixEnd_3365147 := by exact prefixLift 3365147
  have htrace : WordTrace (prefixWord ++ tailWord_3365147) baseStart_3365147 baseEnd_3365147 := by
    simpa [prefixWord, tailWord_3365147, baseEnd_3365147] using wordTrace_append hprefix tailTrace_3365147
  have hstable : (prefixWord ++ tailWord_3365147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365147).length < 2 ^ (prefixWord ++ tailWord_3365147).sum := by decide
  have hdescent : baseEnd_3365147 < baseStart_3365147 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365175 : List Nat := [1, 1, 3, 1, 2, 1, 1, 4, 1, 7]
def baseStart_3365175 : Nat := 118140960795 + 3365175 * 2 ^ 59
def prefixEnd_3365175 : Nat := 4983230072969 + 3 ^ 40 * 3365175 * 2
def baseEnd_3365175 : Nat := 1151968174329317647357565

theorem tailTrace_3365175 : CollatzResearch.WordTrace tailWord_3365175 prefixEnd_3365175 1151968174329317647357565 := by
  unfold tailWord_3365175
  simp only [CollatzResearch.WordTrace]
  refine ⟨122738015583553175978824979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81825343722368783985883319 122738015583553175978824979)
  ·
    refine ⟨184107023375329763968237469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122738015583553175978824979 184107023375329763968237469)
    ·
      refine ⟨69040133765748661488089051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184107023375329763968237469 69040133765748661488089051)
      ·
        refine ⟨103560200648622992232133577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69040133765748661488089051 103560200648622992232133577)
        ·
          refine ⟨77670150486467244174100183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103560200648622992232133577 77670150486467244174100183)
          ·
            refine ⟨116505225729700866261150275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77670150486467244174100183 116505225729700866261150275)
            ·
              refine ⟨174757838594551299391725413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116505225729700866261150275 174757838594551299391725413)
              ·
                refine ⟨32767094736478368635948515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 174757838594551299391725413 32767094736478368635948515)
                ·
                  refine ⟨49150642104717552953922773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32767094736478368635948515 49150642104717552953922773)
                  ·
                    refine ⟨1151968174329317647357565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49150642104717552953922773 1151968174329317647357565)
                    ·
                      rfl

theorem cell22_3365175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 7].length) (baseStart_3365175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3365175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3365175 prefixEnd_3365175 := by exact prefixLift 3365175
  have htrace : WordTrace (prefixWord ++ tailWord_3365175) baseStart_3365175 baseEnd_3365175 := by
    simpa [prefixWord, tailWord_3365175, baseEnd_3365175] using wordTrace_append hprefix tailTrace_3365175
  have hstable : (prefixWord ++ tailWord_3365175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365175).length < 2 ^ (prefixWord ++ tailWord_3365175).sum := by decide
  have hdescent : baseEnd_3365175 < baseStart_3365175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365177 : List Nat := [1, 2, 1, 6, 1, 1, 1, 2, 7]
def baseStart_3365177 : Nat := 118140960795 + 3365177 * 2 ^ 59
def prefixEnd_3365177 : Nat := 4983230072969 + 3 ^ 40 * 3365177 * 2
def baseEnd_3365177 : Nat := 383989619656730102935853

theorem tailTrace_3365177 : CollatzResearch.WordTrace tailWord_3365177 prefixEnd_3365177 383989619656730102935853 := by
  unfold tailWord_3365177
  simp only [CollatzResearch.WordTrace]
  refine ⟨122738088529545930320397785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81825392353030620213598523 122738088529545930320397785)
  ·
    refine ⟨92053566397159447740298339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122738088529545930320397785 92053566397159447740298339)
    ·
      refine ⟨138080349595739171610447509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92053566397159447740298339 138080349595739171610447509)
      ·
        refine ⟨6472516387300273669239727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 138080349595739171610447509 6472516387300273669239727)
        ·
          refine ⟨9708774580950410503859591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6472516387300273669239727 9708774580950410503859591)
          ·
            refine ⟨14563161871425615755789387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9708774580950410503859591 14563161871425615755789387)
            ·
              refine ⟨21844742807138423633684081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14563161871425615755789387 21844742807138423633684081)
              ·
                refine ⟨16383557105353817725263061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21844742807138423633684081 16383557105353817725263061)
                ·
                  refine ⟨383989619656730102935853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16383557105353817725263061 383989619656730102935853)
                  ·
                    rfl

theorem cell22_3365177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 7].length) (baseStart_3365177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3365177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3365177 prefixEnd_3365177 := by exact prefixLift 3365177
  have htrace : WordTrace (prefixWord ++ tailWord_3365177) baseStart_3365177 baseEnd_3365177 := by
    simpa [prefixWord, tailWord_3365177, baseEnd_3365177] using wordTrace_append hprefix tailTrace_3365177
  have hstable : (prefixWord ++ tailWord_3365177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365177).length < 2 ^ (prefixWord ++ tailWord_3365177).sum := by decide
  have hdescent : baseEnd_3365177 < baseStart_3365177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365207 : List Nat := [1, 1, 3, 2, 3, 1, 2, 2, 3, 4]
def baseStart_3365207 : Nat := 118140960795 + 3365207 * 2 ^ 59
def prefixEnd_3365207 : Nat := 4983230072969 + 3 ^ 40 * 3365207 * 2
def baseEnd_3365207 : Nat := 1151979128583280230557467

theorem tailTrace_3365207 : CollatzResearch.WordTrace tailWord_3365207 prefixEnd_3365207 1151979128583280230557467 := by
  unfold tailWord_3365207
  simp only [CollatzResearch.WordTrace]
  refine ⟨122739182719437245443989875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81826121812958163629326583 122739182719437245443989875)
  ·
    refine ⟨184108774079155868165984813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122739182719437245443989875 184108774079155868165984813)
    ·
      refine ⟨69040790279683450562244305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184108774079155868165984813 69040790279683450562244305)
      ·
        refine ⟨51780592709762587921683229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69040790279683450562244305 51780592709762587921683229)
        ·
          refine ⟨19417722266160970470631211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51780592709762587921683229 19417722266160970470631211)
          ·
            refine ⟨29126583399241455705946817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19417722266160970470631211 29126583399241455705946817)
            ·
              refine ⟨21844937549431091779460113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29126583399241455705946817 21844937549431091779460113)
              ·
                refine ⟨16383703162073318834595085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21844937549431091779460113 16383703162073318834595085)
                ·
                  refine ⟨6143888685777494562973157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16383703162073318834595085 6143888685777494562973157)
                  ·
                    refine ⟨1151979128583280230557467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6143888685777494562973157 1151979128583280230557467)
                    ·
                      rfl

theorem cell22_3365207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 3, 4].length) (baseStart_3365207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3365207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3365207 prefixEnd_3365207 := by exact prefixLift 3365207
  have htrace : WordTrace (prefixWord ++ tailWord_3365207) baseStart_3365207 baseEnd_3365207 := by
    simpa [prefixWord, tailWord_3365207, baseEnd_3365207] using wordTrace_append hprefix tailTrace_3365207
  have hstable : (prefixWord ++ tailWord_3365207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365207).length < 2 ^ (prefixWord ++ tailWord_3365207).sum := by decide
  have hdescent : baseEnd_3365207 < baseStart_3365207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365224 : List Nat := [2, 1, 4, 2, 2, 2, 1, 1, 3, 4]
def baseStart_3365224 : Nat := 118140960795 + 3365224 * 2 ^ 59
def prefixEnd_3365224 : Nat := 4983230072969 + 3 ^ 40 * 3365224 * 2
def baseEnd_3365224 : Nat := 1151984948030697852882415

theorem tailTrace_3365224 : CollatzResearch.WordTrace tailWord_3365224 prefixEnd_3365224 1151984948030697852882415 := by
  unfold tailWord_3365224
  simp only [CollatzResearch.WordTrace]
  refine ⟨61369901380187828673679363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81826535173583771564905817 61369901380187828673679363)
  ·
    refine ⟨92054852070281743010519045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61369901380187828673679363 92054852070281743010519045)
    ·
      refine ⟨17260284763177826814472321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92054852070281743010519045 17260284763177826814472321)
      ·
        refine ⟨12945213572383370110854241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17260284763177826814472321 12945213572383370110854241)
        ·
          refine ⟨9708910179287527583140681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12945213572383370110854241 9708910179287527583140681)
          ·
            refine ⟨7281682634465645687355511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9708910179287527583140681 7281682634465645687355511)
            ·
              refine ⟨10922523951698468531033267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7281682634465645687355511 10922523951698468531033267)
              ·
                refine ⟨16383785927547702796549901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10922523951698468531033267 16383785927547702796549901)
                ·
                  refine ⟨6143919722830388548706213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16383785927547702796549901 6143919722830388548706213)
                  ·
                    refine ⟨1151984948030697852882415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6143919722830388548706213 1151984948030697852882415)
                    ·
                      rfl

theorem cell22_3365224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_3365224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3365224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3365224 prefixEnd_3365224 := by exact prefixLift 3365224
  have htrace : WordTrace (prefixWord ++ tailWord_3365224) baseStart_3365224 baseEnd_3365224 := by
    simpa [prefixWord, tailWord_3365224, baseEnd_3365224] using wordTrace_append hprefix tailTrace_3365224
  have hstable : (prefixWord ++ tailWord_3365224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365224).length < 2 ^ (prefixWord ++ tailWord_3365224).sum := by decide
  have hdescent : baseEnd_3365224 < baseStart_3365224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365436 : List Nat := [2, 2, 2, 2, 3, 3, 1, 7]
def baseStart_3365436 : Nat := 118140960795 + 3365436 * 2 ^ 59
def prefixEnd_3365436 : Nat := 4983230072969 + 3 ^ 40 * 3365436 * 2
def baseEnd_3365436 : Nat := 128006391107022218509085

theorem tailTrace_3365436 : CollatzResearch.WordTrace tailWord_3365436 prefixEnd_3365436 128006391107022218509085 := by
  unfold tailWord_3365436
  simp only [CollatzResearch.WordTrace]
  refine ⟨61373767517803808777038081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81831690023738411702717441 61373767517803808777038081)
  ·
    refine ⟨46030325638352856582778561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61373767517803808777038081 46030325638352856582778561)
    ·
      refine ⟨34522744228764642437083921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46030325638352856582778561 34522744228764642437083921)
      ·
        refine ⟨25892058171573481827812941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34522744228764642437083921 25892058171573481827812941)
        ·
          refine ⟨9709521814340055685429853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25892058171573481827812941 9709521814340055685429853)
          ·
            refine ⟨3641070680377520882036195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9709521814340055685429853 3641070680377520882036195)
            ·
              refine ⟨5461606020566281323054293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3641070680377520882036195 5461606020566281323054293)
              ·
                refine ⟨128006391107022218509085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5461606020566281323054293 128006391107022218509085)
                ·
                  rfl

theorem cell22_3365436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 7].length) (baseStart_3365436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3365436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3365436 prefixEnd_3365436 := by exact prefixLift 3365436
  have htrace : WordTrace (prefixWord ++ tailWord_3365436) baseStart_3365436 baseEnd_3365436 := by
    simpa [prefixWord, tailWord_3365436, baseEnd_3365436] using wordTrace_append hprefix tailTrace_3365436
  have hstable : (prefixWord ++ tailWord_3365436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365436).length < 2 ^ (prefixWord ++ tailWord_3365436).sum := by decide
  have hdescent : baseEnd_3365436 < baseStart_3365436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365453 : List Nat := [1, 6, 1, 1, 2, 2, 3, 6]
def baseStart_3365453 : Nat := 118140960795 + 3365453 * 2 ^ 59
def prefixEnd_3365453 : Nat := 4983230072969 + 3 ^ 40 * 3365453 * 2
def baseEnd_3365453 : Nat := 128007037712290843211857

theorem tailTrace_3365453 : CollatzResearch.WordTrace tailWord_3365453 prefixEnd_3365453 128007037712290843211857 := by
  unfold tailWord_3365453
  simp only [CollatzResearch.WordTrace]
  refine ⟨122748155076546029457445013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81832103384364019638296675 122748155076546029457445013)
  ·
    refine ⟨5753819769213095130817735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 122748155076546029457445013 5753819769213095130817735)
    ·
      refine ⟨8630729653819642696226603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5753819769213095130817735 8630729653819642696226603)
      ·
        refine ⟨12946094480729464044339905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8630729653819642696226603 12946094480729464044339905)
        ·
          refine ⟨9709570860547098033254929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12946094480729464044339905 9709570860547098033254929)
          ·
            refine ⟨7282178145410323524941197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9709570860547098033254929 7282178145410323524941197)
            ·
              refine ⟨2730816804528871321852949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7282178145410323524941197 2730816804528871321852949)
              ·
                refine ⟨128007037712290843211857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2730816804528871321852949 128007037712290843211857)
                ·
                  rfl

theorem cell22_3365453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3, 6].length) (baseStart_3365453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3365453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3365453 prefixEnd_3365453 := by exact prefixLift 3365453
  have htrace : WordTrace (prefixWord ++ tailWord_3365453) baseStart_3365453 baseEnd_3365453 := by
    simpa [prefixWord, tailWord_3365453, baseEnd_3365453] using wordTrace_append hprefix tailTrace_3365453
  have hstable : (prefixWord ++ tailWord_3365453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365453).length < 2 ^ (prefixWord ++ tailWord_3365453).sum := by decide
  have hdescent : baseEnd_3365453 < baseStart_3365453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365470 : List Nat := [4, 4, 1, 2, 1, 1, 9]
def baseStart_3365470 : Nat := 118140960795 + 3365470 * 2 ^ 59
def prefixEnd_3365470 : Nat := 4983230072969 + 3 ^ 40 * 3365470 * 2
def baseEnd_3365470 : Nat := 42669228105853155971543

theorem tailTrace_3365470 : CollatzResearch.WordTrace tailWord_3365470 prefixEnd_3365470 42669228105853155971543 := by
  unfold tailWord_3365470
  simp only [CollatzResearch.WordTrace]
  refine ⟨15343596889685555170101733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81832516744989627573875909 15343596889685555170101733)
  ·
    refine ⟨2876924416816041594394075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15343596889685555170101733 2876924416816041594394075)
    ·
      refine ⟨4315386625224062391591113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2876924416816041594394075 4315386625224062391591113)
      ·
        refine ⟨3236539968918046793693335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4315386625224062391591113 3236539968918046793693335)
        ·
          refine ⟨4854809953377070190540003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3236539968918046793693335 4854809953377070190540003)
          ·
            refine ⟨7282214930065605285810005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4854809953377070190540003 7282214930065605285810005)
            ·
              refine ⟨42669228105853155971543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7282214930065605285810005 42669228105853155971543)
              ·
                rfl

theorem cell22_3365470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 9].length) (baseStart_3365470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3365470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3365470 prefixEnd_3365470 := by exact prefixLift 3365470
  have htrace : WordTrace (prefixWord ++ tailWord_3365470) baseStart_3365470 baseEnd_3365470 := by
    simpa [prefixWord, tailWord_3365470, baseEnd_3365470] using wordTrace_append hprefix tailTrace_3365470
  have hstable : (prefixWord ++ tailWord_3365470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365470).length < 2 ^ (prefixWord ++ tailWord_3365470).sum := by decide
  have hdescent : baseEnd_3365470 < baseStart_3365470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365474 : List Nat := [3, 3, 2, 3, 2, 1, 1, 2, 2, 3]
def baseStart_3365474 : Nat := 118140960795 + 3365474 * 2 ^ 59
def prefixEnd_3365474 : Nat := 4983230072969 + 3 ^ 40 * 3365474 * 2
def baseEnd_3365474 : Nat := 1152070528139780534131649

theorem tailTrace_3365474 : CollatzResearch.WordTrace tailWord_3365474 prefixEnd_3365474 1152070528139780534131649 := by
  unfold tailWord_3365474
  simp only [CollatzResearch.WordTrace]
  refine ⟨30687230252367487510989869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81832614006313300029306317 30687230252367487510989869)
  ·
    refine ⟨11507711344637807816621201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30687230252367487510989869 11507711344637807816621201)
    ·
      refine ⟨8630783508478355862465901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11507711344637807816621201 8630783508478355862465901)
      ·
        refine ⟨3236543815679383448424713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8630783508478355862465901 3236543815679383448424713)
        ·
          refine ⟨2427407861759537586318535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3236543815679383448424713 2427407861759537586318535)
          ·
            refine ⟨3641111792639306379477803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2427407861759537586318535 3641111792639306379477803)
            ·
              refine ⟨5461667688958959569216705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3641111792639306379477803 5461667688958959569216705)
              ·
                refine ⟨4096250766719219676912529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5461667688958959569216705 4096250766719219676912529)
                ·
                  refine ⟨3072188075039414757684397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4096250766719219676912529 3072188075039414757684397)
                  ·
                    refine ⟨1152070528139780534131649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3072188075039414757684397 1152070528139780534131649)
                    ·
                      rfl

theorem cell22_3365474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_3365474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3365474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3365474 prefixEnd_3365474 := by exact prefixLift 3365474
  have htrace : WordTrace (prefixWord ++ tailWord_3365474) baseStart_3365474 baseEnd_3365474 := by
    simpa [prefixWord, tailWord_3365474, baseEnd_3365474] using wordTrace_append hprefix tailTrace_3365474
  have hstable : (prefixWord ++ tailWord_3365474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365474).length < 2 ^ (prefixWord ++ tailWord_3365474).sum := by decide
  have hdescent : baseEnd_3365474 < baseStart_3365474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365485 : List Nat := [1, 5, 1, 1, 3, 1, 2, 4, 1, 3]
def baseStart_3365485 : Nat := 118140960795 + 3365485 * 2 ^ 59
def prefixEnd_3365485 : Nat := 4983230072969 + 3 ^ 40 * 3365485 * 2
def baseEnd_3365485 : Nat := 1152074293664580172106615

theorem tailTrace_3365485 : CollatzResearch.WordTrace tailWord_3365485 prefixEnd_3365485 1152074293664580172106615 := by
  unfold tailWord_3365485
  simp only [CollatzResearch.WordTrace]
  refine ⟨122749322212430098922609909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81832881474953399281739939 122749322212430098922609909)
  ·
    refine ⟨11507748957415321773994679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 122749322212430098922609909 11507748957415321773994679)
    ·
      refine ⟨17261623436122982660992019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11507748957415321773994679 17261623436122982660992019)
      ·
        refine ⟨25892435154184473991488029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17261623436122982660992019 25892435154184473991488029)
        ·
          refine ⟨9709663182819177746808011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25892435154184473991488029 9709663182819177746808011)
          ·
            refine ⟨14564494774228766620212017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9709663182819177746808011 14564494774228766620212017)
            ·
              refine ⟨10923371080671574965159013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14564494774228766620212017 10923371080671574965159013)
              ·
                refine ⟨2048132077625920305967315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10923371080671574965159013 2048132077625920305967315)
                ·
                  refine ⟨3072198116438880458950973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2048132077625920305967315 3072198116438880458950973)
                  ·
                    refine ⟨1152074293664580172106615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3072198116438880458950973 1152074293664580172106615)
                    ·
                      rfl

theorem cell22_3365485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 4, 1, 3].length) (baseStart_3365485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3365485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3365485 prefixEnd_3365485 := by exact prefixLift 3365485
  have htrace : WordTrace (prefixWord ++ tailWord_3365485) baseStart_3365485 baseEnd_3365485 := by
    simpa [prefixWord, tailWord_3365485, baseEnd_3365485] using wordTrace_append hprefix tailTrace_3365485
  have hstable : (prefixWord ++ tailWord_3365485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365485).length < 2 ^ (prefixWord ++ tailWord_3365485).sum := by decide
  have hdescent : baseEnd_3365485 < baseStart_3365485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365539 : List Nat := [1, 1, 1, 4, 1, 1, 2, 2, 3, 6]
def baseStart_3365539 : Nat := 118140960795 + 3365539 * 2 ^ 59
def prefixEnd_3365539 : Nat := 4983230072969 + 3 ^ 40 * 3365539 * 2
def baseEnd_3365539 : Nat := 1152092778968142031256449

theorem tailTrace_3365539 : CollatzResearch.WordTrace tailWord_3365539 prefixEnd_3365539 1152092778968142031256449 := by
  unfold tailWord_3365539
  simp only [CollatzResearch.WordTrace]
  refine ⟨122751291754234466145075671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81834194502822977430050447 122751291754234466145075671)
  ·
    refine ⟨184126937631351699217613507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122751291754234466145075671 184126937631351699217613507)
    ·
      refine ⟨276190406447027548826420261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184126937631351699217613507 276190406447027548826420261)
      ·
        refine ⟨51785701208817665404953799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 276190406447027548826420261 51785701208817665404953799)
        ·
          refine ⟨77678551813226498107430699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51785701208817665404953799 77678551813226498107430699)
          ·
            refine ⟨116517827719839747161146049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77678551813226498107430699 116517827719839747161146049)
            ·
              refine ⟨87388370789879810370859537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116517827719839747161146049 87388370789879810370859537)
              ·
                refine ⟨65541278092409857778144653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87388370789879810370859537 65541278092409857778144653)
                ·
                  refine ⟨24577979284653696666804245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65541278092409857778144653 24577979284653696666804245)
                  ·
                    refine ⟨1152092778968142031256449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24577979284653696666804245 1152092778968142031256449)
                    ·
                      rfl

theorem cell22_3365539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 6].length) (baseStart_3365539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3365539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3365539 prefixEnd_3365539 := by exact prefixLift 3365539
  have htrace : WordTrace (prefixWord ++ tailWord_3365539) baseStart_3365539 baseEnd_3365539 := by
    simpa [prefixWord, tailWord_3365539, baseEnd_3365539] using wordTrace_append hprefix tailTrace_3365539
  have hstable : (prefixWord ++ tailWord_3365539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365539).length < 2 ^ (prefixWord ++ tailWord_3365539).sum := by decide
  have hdescent : baseEnd_3365539 < baseStart_3365539 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365588 : List Nat := [2, 4, 1, 3, 3, 9]
def baseStart_3365588 : Nat := 118140960795 + 3365588 * 2 ^ 59
def prefixEnd_3365588 : Nat := 4983230072969 + 3 ^ 40 * 3365588 * 2
def baseEnd_3365588 : Nat := 14223574724315089342979

theorem tailTrace_3365588 : CollatzResearch.WordTrace tailWord_3365588 prefixEnd_3365588 14223574724315089342979 := by
  unfold tailWord_3365588
  simp only [CollatzResearch.WordTrace]
  refine ⟨61376539465528473756804709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81835385954037965009072945 61376539465528473756804709)
  ·
    refine ⟨11508101149786588829400883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61376539465528473756804709 11508101149786588829400883)
    ·
      refine ⟨17262151724679883244101325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11508101149786588829400883 17262151724679883244101325)
      ·
        refine ⟨6473306896754956216537997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17262151724679883244101325 6473306896754956216537997)
        ·
          refine ⟨2427490086283108581201749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6473306896754956216537997 2427490086283108581201749)
          ·
            refine ⟨14223574724315089342979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2427490086283108581201749 14223574724315089342979)
            ·
              rfl

theorem cell22_3365588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 9].length) (baseStart_3365588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3365588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3365588 prefixEnd_3365588 := by exact prefixLift 3365588
  have htrace : WordTrace (prefixWord ++ tailWord_3365588) baseStart_3365588 baseEnd_3365588 := by
    simpa [prefixWord, tailWord_3365588, baseEnd_3365588] using wordTrace_append hprefix tailTrace_3365588
  have hstable : (prefixWord ++ tailWord_3365588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365588).length < 2 ^ (prefixWord ++ tailWord_3365588).sum := by decide
  have hdescent : baseEnd_3365588 < baseStart_3365588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365601 : List Nat := [1, 2, 3, 1, 4, 1, 1, 1, 2, 6]
def baseStart_3365601 : Nat := 118140960795 + 3365601 * 2 ^ 59
def prefixEnd_3365601 : Nat := 4983230072969 + 3 ^ 40 * 3365601 * 2
def baseEnd_3365601 : Nat := 1152114002835194536206259

theorem tailTrace_3365601 : CollatzResearch.WordTrace tailWord_3365601 prefixEnd_3365601 1152114002835194536206259 := by
  unfold tailWord_3365601
  simp only [CollatzResearch.WordTrace]
  refine ⟨122753553080009850733832657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81835702053339900489221771 122753553080009850733832657)
  ·
    refine ⟨92065164810007388050374493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122753553080009850733832657 92065164810007388050374493)
    ·
      refine ⟨34524436803752770518890435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92065164810007388050374493 34524436803752770518890435)
      ·
        refine ⟨51786655205629155778335653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34524436803752770518890435 51786655205629155778335653)
        ·
          refine ⟨9709997851055466708437935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51786655205629155778335653 9709997851055466708437935)
          ·
            refine ⟨14564996776583200062656903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9709997851055466708437935 14564996776583200062656903)
            ·
              refine ⟨21847495164874800093985355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14564996776583200062656903 21847495164874800093985355)
              ·
                refine ⟨32771242747312200140978033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21847495164874800093985355 32771242747312200140978033)
                ·
                  refine ⟨24578432060484150105733525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32771242747312200140978033 24578432060484150105733525)
                  ·
                    refine ⟨1152114002835194536206259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24578432060484150105733525 1152114002835194536206259)
                    ·
                      rfl

theorem cell22_3365601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_3365601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3365601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3365601 prefixEnd_3365601 := by exact prefixLift 3365601
  have htrace : WordTrace (prefixWord ++ tailWord_3365601) baseStart_3365601 baseEnd_3365601 := by
    simpa [prefixWord, tailWord_3365601, baseEnd_3365601] using wordTrace_append hprefix tailTrace_3365601
  have hstable : (prefixWord ++ tailWord_3365601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365601).length < 2 ^ (prefixWord ++ tailWord_3365601).sum := by decide
  have hdescent : baseEnd_3365601 < baseStart_3365601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365616 : List Nat := [2, 1, 1, 1, 3, 1, 3, 5, 5]
def baseStart_3365616 : Nat := 118140960795 + 3365616 * 2 ^ 59
def prefixEnd_3365616 : Nat := 4983230072969 + 3 ^ 40 * 3365616 * 2
def baseEnd_3365616 : Nat := 384039712547246499027071

theorem tailTrace_3365616 : CollatzResearch.WordTrace tailWord_3365616 prefixEnd_3365616 384039712547246499027071 := by
  unfold tailWord_3365616
  simp only [CollatzResearch.WordTrace]
  refine ⟨61377050087477754147814351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81836066783303672197085801 61377050087477754147814351)
  ·
    refine ⟨92065575131216631221721527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61377050087477754147814351 92065575131216631221721527)
    ·
      refine ⟨138098362696824946832582291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92065575131216631221721527 138098362696824946832582291)
      ·
        refine ⟨207147544045237420248873437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138098362696824946832582291 207147544045237420248873437)
        ·
          refine ⟨77680329016964032593327539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207147544045237420248873437 77680329016964032593327539)
          ·
            refine ⟨116520493525446048889991309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77680329016964032593327539 116520493525446048889991309)
            ·
              refine ⟨43695185072042268333746741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116520493525446048889991309 43695185072042268333746741)
              ·
                refine ⟨4096423600503962656288757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43695185072042268333746741 4096423600503962656288757)
                ·
                  refine ⟨384039712547246499027071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4096423600503962656288757 384039712547246499027071)
                  ·
                    rfl

theorem cell22_3365616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 5, 5].length) (baseStart_3365616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3365616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3365616 prefixEnd_3365616 := by exact prefixLift 3365616
  have htrace : WordTrace (prefixWord ++ tailWord_3365616) baseStart_3365616 baseEnd_3365616 := by
    simpa [prefixWord, tailWord_3365616, baseEnd_3365616] using wordTrace_append hprefix tailTrace_3365616
  have hstable : (prefixWord ++ tailWord_3365616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365616).length < 2 ^ (prefixWord ++ tailWord_3365616).sum := by decide
  have hdescent : baseEnd_3365616 < baseStart_3365616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365650 : List Nat := [3, 2, 4, 1, 2, 1, 1, 1, 7]
def baseStart_3365650 : Nat := 118140960795 + 3365650 * 2 ^ 59
def prefixEnd_3365650 : Nat := 4983230072969 + 3 ^ 40 * 3365650 * 2
def baseEnd_3365650 : Nat := 384043592178858247243703

theorem tailTrace_3365650 : CollatzResearch.WordTrace tailWord_3365650 prefixEnd_3365650 384043592178858247243703 := by
  unfold tailWord_3365650
  simp only [CollatzResearch.WordTrace]
  refine ⟨30688835064208083025591601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81836893504554888068244269 30688835064208083025591601)
  ·
    refine ⟨23016626298156062269193701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30688835064208083025591601 23016626298156062269193701)
    ·
      refine ⟨4315617430904261675473819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23016626298156062269193701 4315617430904261675473819)
      ·
        refine ⟨6473426146356392513210729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4315617430904261675473819 6473426146356392513210729)
        ·
          refine ⟨4855069609767294384908047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6473426146356392513210729 4855069609767294384908047)
          ·
            refine ⟨7282604414650941577362071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4855069609767294384908047 7282604414650941577362071)
            ·
              refine ⟨10923906621976412366043107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7282604414650941577362071 10923906621976412366043107)
              ·
                refine ⟨16385859932964618549064661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10923906621976412366043107 16385859932964618549064661)
                ·
                  refine ⟨384043592178858247243703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16385859932964618549064661 384043592178858247243703)
                  ·
                    rfl

theorem cell22_3365650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 7].length) (baseStart_3365650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3365650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3365650 prefixEnd_3365650 := by exact prefixLift 3365650
  have htrace : WordTrace (prefixWord ++ tailWord_3365650) baseStart_3365650 baseEnd_3365650 := by
    simpa [prefixWord, tailWord_3365650, baseEnd_3365650] using wordTrace_append hprefix tailTrace_3365650
  have hstable : (prefixWord ++ tailWord_3365650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365650).length < 2 ^ (prefixWord ++ tailWord_3365650).sum := by decide
  have hdescent : baseEnd_3365650 < baseStart_3365650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365695 : List Nat := [1, 1, 2, 2, 5, 1, 3, 3, 4]
def baseStart_3365695 : Nat := 118140960795 + 3365695 * 2 ^ 59
def prefixEnd_3365695 : Nat := 4983230072969 + 3 ^ 40 * 3365695 * 2
def baseEnd_3365695 : Nat := 384048726985403208118657

theorem tailTrace_3365695 : CollatzResearch.WordTrace tailWord_3365695 prefixEnd_3365695 384048726985403208118657 := by
  unfold tailWord_3365695
  simp only [CollatzResearch.WordTrace]
  refine ⟨122756981541669304787754539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81837987694446203191836359 122756981541669304787754539)
  ·
    refine ⟨184135472312503957181631809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122756981541669304787754539 184135472312503957181631809)
    ·
      refine ⟨138101604234377967886223857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184135472312503957181631809 138101604234377967886223857)
      ·
        refine ⟨103576203175783475914667893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138101604234377967886223857 103576203175783475914667893)
        ·
          refine ⟨9710269047729700867000115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 103576203175783475914667893 9710269047729700867000115)
          ·
            refine ⟨14565403571594551300500173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9710269047729700867000115 14565403571594551300500173)
            ·
              refine ⟨5462026339347956737687565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14565403571594551300500173 5462026339347956737687565)
              ·
                refine ⟨2048259877255483776632837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5462026339347956737687565 2048259877255483776632837)
                ·
                  refine ⟨384048726985403208118657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2048259877255483776632837 384048726985403208118657)
                  ·
                    rfl

theorem cell22_3365695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 3, 4].length) (baseStart_3365695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3365695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3365695 prefixEnd_3365695 := by exact prefixLift 3365695
  have htrace : WordTrace (prefixWord ++ tailWord_3365695) baseStart_3365695 baseEnd_3365695 := by
    simpa [prefixWord, tailWord_3365695, baseEnd_3365695] using wordTrace_append hprefix tailTrace_3365695
  have hstable : (prefixWord ++ tailWord_3365695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365695).length < 2 ^ (prefixWord ++ tailWord_3365695).sum := by decide
  have hdescent : baseEnd_3365695 < baseStart_3365695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365708 : List Nat := [2, 2, 1, 3, 3, 1, 1, 1, 4, 4]
def baseStart_3365708 : Nat := 118140960795 + 3365708 * 2 ^ 59
def prefixEnd_3365708 : Nat := 4983230072969 + 3 ^ 40 * 3365708 * 2
def baseEnd_3365708 : Nat := 1152150631121881923780931

theorem tailTrace_3365708 : CollatzResearch.WordTrace tailWord_3365708 prefixEnd_3365708 1152150631121881923780931 := by
  unfold tailWord_3365708
  simp only [CollatzResearch.WordTrace]
  refine ⟨61378727845311104003988889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81838303793748138671985185 61378727845311104003988889)
  ·
    refine ⟨46034045883983328002991667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61378727845311104003988889 46034045883983328002991667)
    ·
      refine ⟨69051068825974992004487501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46034045883983328002991667 69051068825974992004487501)
      ·
        refine ⟨25894150809740622001682813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69051068825974992004487501 25894150809740622001682813)
        ·
          refine ⟨9710306553652733250631055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25894150809740622001682813 9710306553652733250631055)
          ·
            refine ⟨14565459830479099875946583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9710306553652733250631055 14565459830479099875946583)
            ·
              refine ⟨21848189745718649813919875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14565459830479099875946583 21848189745718649813919875)
              ·
                refine ⟨32772284618577974720879813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21848189745718649813919875 32772284618577974720879813)
                ·
                  refine ⟨6144803365983370260164965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32772284618577974720879813 6144803365983370260164965)
                  ·
                    refine ⟨1152150631121881923780931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6144803365983370260164965 1152150631121881923780931)
                    ·
                      rfl

theorem cell22_3365708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 4, 4].length) (baseStart_3365708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3365708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3365708 prefixEnd_3365708 := by exact prefixLift 3365708
  have htrace : WordTrace (prefixWord ++ tailWord_3365708) baseStart_3365708 baseEnd_3365708 := by
    simpa [prefixWord, tailWord_3365708, baseEnd_3365708] using wordTrace_append hprefix tailTrace_3365708
  have hstable : (prefixWord ++ tailWord_3365708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365708).length < 2 ^ (prefixWord ++ tailWord_3365708).sum := by decide
  have hdescent : baseEnd_3365708 < baseStart_3365708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365742 : List Nat := [4, 1, 2, 3, 2, 1, 2, 1, 2, 4]
def baseStart_3365742 : Nat := 118140960795 + 3365742 * 2 ^ 59
def prefixEnd_3365742 : Nat := 4983230072969 + 3 ^ 40 * 3365742 * 2
def baseEnd_3365742 : Nat := 1152162270016717168430827

theorem tailTrace_3365742 : CollatzResearch.WordTrace tailWord_3365742 prefixEnd_3365742 1152162270016717168430827 := by
  unfold tailWord_3365742
  simp only [CollatzResearch.WordTrace]
  refine ⟨15344836971562378976839435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81839130514999354543143653 15344836971562378976839435)
  ·
    refine ⟨23017255457343568465259153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15344836971562378976839435 23017255457343568465259153)
    ·
      refine ⟨17262941593007676348944365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23017255457343568465259153 17262941593007676348944365)
      ·
        refine ⟨6473603097377878630854137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17262941593007676348944365 6473603097377878630854137)
        ·
          refine ⟨4855202323033408973140603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6473603097377878630854137 4855202323033408973140603)
          ·
            refine ⟨7282803484550113459710905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4855202323033408973140603 7282803484550113459710905)
            ·
              refine ⟨5462102613412585094783179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7282803484550113459710905 5462102613412585094783179)
              ·
                refine ⟨8193153920118877642174769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5462102613412585094783179 8193153920118877642174769)
                ·
                  refine ⟨6144865440089158231631077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8193153920118877642174769 6144865440089158231631077)
                  ·
                    refine ⟨1152162270016717168430827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6144865440089158231631077 1152162270016717168430827)
                    ·
                      rfl

theorem cell22_3365742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_3365742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3365742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3365742 prefixEnd_3365742 := by exact prefixLift 3365742
  have htrace : WordTrace (prefixWord ++ tailWord_3365742) baseStart_3365742 baseEnd_3365742 := by
    simpa [prefixWord, tailWord_3365742, baseEnd_3365742] using wordTrace_append hprefix tailTrace_3365742
  have hstable : (prefixWord ++ tailWord_3365742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365742).length < 2 ^ (prefixWord ++ tailWord_3365742).sum := by decide
  have hdescent : baseEnd_3365742 < baseStart_3365742 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365751 : List Nat := [1, 1, 3, 1, 1, 2, 1, 3, 9]
def baseStart_3365751 : Nat := 118140960795 + 3365751 * 2 ^ 59
def prefixEnd_3365751 : Nat := 4983230072969 + 3 ^ 40 * 3365751 * 2
def baseEnd_3365751 : Nat := 384055116966881381651933

theorem tailTrace_3365751 : CollatzResearch.WordTrace tailWord_3365751 prefixEnd_3365751 384055116966881381651933 := by
  unfold tailWord_3365751
  simp only [CollatzResearch.WordTrace]
  refine ⟨122759024029466426351793107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81839349352977617567862071 122759024029466426351793107)
  ·
    refine ⟨184138536044199639527689661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122759024029466426351793107 184138536044199639527689661)
    ·
      refine ⟨69051951016574864822883623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184138536044199639527689661 69051951016574864822883623)
      ·
        refine ⟨103577926524862297234325435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69051951016574864822883623 103577926524862297234325435)
        ·
          refine ⟨155366889787293445851488153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103577926524862297234325435 155366889787293445851488153)
          ·
            refine ⟨116525167340470084388616115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155366889787293445851488153 116525167340470084388616115)
            ·
              refine ⟨174787751010705126582924173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116525167340470084388616115 174787751010705126582924173)
              ·
                refine ⟨65545406629014422468596565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 174787751010705126582924173 65545406629014422468596565)
                ·
                  refine ⟨384055116966881381651933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 65545406629014422468596565 384055116966881381651933)
                  ·
                    rfl

theorem cell22_3365751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 9].length) (baseStart_3365751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3365751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3365751 prefixEnd_3365751 := by exact prefixLift 3365751
  have htrace : WordTrace (prefixWord ++ tailWord_3365751) baseStart_3365751 baseEnd_3365751 := by
    simpa [prefixWord, tailWord_3365751, baseEnd_3365751] using wordTrace_append hprefix tailTrace_3365751
  have hstable : (prefixWord ++ tailWord_3365751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365751).length < 2 ^ (prefixWord ++ tailWord_3365751).sum := by decide
  have hdescent : baseEnd_3365751 < baseStart_3365751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365783 : List Nat := [1, 1, 3, 3, 1, 2, 3, 1, 2, 5]
def baseStart_3365783 : Nat := 118140960795 + 3365783 * 2 ^ 59
def prefixEnd_3365783 : Nat := 4983230072969 + 3 ^ 40 * 3365783 * 2
def baseEnd_3365783 : Nat := 1152176305154606728155701

theorem tailTrace_3365783 : CollatzResearch.WordTrace tailWord_3365783 prefixEnd_3365783 1152176305154606728155701 := by
  unfold tailWord_3365783
  simp only [CollatzResearch.WordTrace]
  refine ⟨122760191165350495816958003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81840127443566997211305335 122760191165350495816958003)
  ·
    refine ⟨184140286748025743725437005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122760191165350495816958003 184140286748025743725437005)
    ·
      refine ⟨69052607530509653897038877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184140286748025743725437005 69052607530509653897038877)
      ·
        refine ⟨25894727823941120211389579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69052607530509653897038877 25894727823941120211389579)
        ·
          refine ⟨38842091735911680317084369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25894727823941120211389579 38842091735911680317084369)
          ·
            refine ⟨29131568801933760237813277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38842091735911680317084369 29131568801933760237813277)
            ·
              refine ⟨10924338300725160089179979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29131568801933760237813277 10924338300725160089179979)
              ·
                refine ⟨16386507451087740133769969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10924338300725160089179979 16386507451087740133769969)
                ·
                  refine ⟨12289880588315805100327477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16386507451087740133769969 12289880588315805100327477)
                  ·
                    refine ⟨1152176305154606728155701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12289880588315805100327477 1152176305154606728155701)
                    ·
                      rfl

theorem cell22_3365783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 2, 5].length) (baseStart_3365783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3365783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3365783 prefixEnd_3365783 := by exact prefixLift 3365783
  have htrace : WordTrace (prefixWord ++ tailWord_3365783) baseStart_3365783 baseEnd_3365783 := by
    simpa [prefixWord, tailWord_3365783, baseEnd_3365783] using wordTrace_append hprefix tailTrace_3365783
  have hstable : (prefixWord ++ tailWord_3365783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365783).length < 2 ^ (prefixWord ++ tailWord_3365783).sum := by decide
  have hdescent : baseEnd_3365783 < baseStart_3365783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365813 : List Nat := [1, 3, 3, 2, 1, 1, 1, 2, 8]
def baseStart_3365813 : Nat := 118140960795 + 3365813 * 2 ^ 59
def prefixEnd_3365813 : Nat := 4983230072969 + 3 ^ 40 * 3365813 * 2
def baseEnd_3365813 : Nat := 384062191589232216635203

theorem tailTrace_3365813 : CollatzResearch.WordTrace tailWord_3365813 prefixEnd_3365813 384062191589232216635203 := by
  unfold tailWord_3365813
  simp only [CollatzResearch.WordTrace]
  refine ⟨122761285355241810940550093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81840856903494540627033395 122761285355241810940550093)
  ·
    refine ⟨46035482008215679102706285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122761285355241810940550093 46035482008215679102706285)
    ·
      refine ⟨17263305753080879663514857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46035482008215679102706285 17263305753080879663514857)
      ·
        refine ⟨12947479314810659747636143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17263305753080879663514857 12947479314810659747636143)
        ·
          refine ⟨19421218972215989621454215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12947479314810659747636143 19421218972215989621454215)
          ·
            refine ⟨29131828458323984432181323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19421218972215989621454215 29131828458323984432181323)
            ·
              refine ⟨43697742687485976648271985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29131828458323984432181323 43697742687485976648271985)
              ·
                refine ⟨32773307015614482486203989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43697742687485976648271985 32773307015614482486203989)
                ·
                  refine ⟨384062191589232216635203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32773307015614482486203989 384062191589232216635203)
                  ·
                    rfl

theorem cell22_3365813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 8].length) (baseStart_3365813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3365813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3365813 prefixEnd_3365813 := by exact prefixLift 3365813
  have htrace : WordTrace (prefixWord ++ tailWord_3365813) baseStart_3365813 baseEnd_3365813 := by
    simpa [prefixWord, tailWord_3365813, baseEnd_3365813] using wordTrace_append hprefix tailTrace_3365813
  have hstable : (prefixWord ++ tailWord_3365813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365813).length < 2 ^ (prefixWord ++ tailWord_3365813).sum := by decide
  have hdescent : baseEnd_3365813 < baseStart_3365813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366147 : List Nat := [1, 1, 1, 3, 2, 5, 1, 1, 1, 6]
def baseStart_3366147 : Nat := 118140960795 + 3366147 * 2 ^ 59
def prefixEnd_3366147 : Nat := 4983230072969 + 3 ^ 40 * 3366147 * 2
def baseEnd_3366147 : Nat := 1152300909793431112054585

theorem tailTrace_3366147 : CollatzResearch.WordTrace tailWord_3366147 prefixEnd_3366147 1152300909793431112054585 := by
  unfold tailWord_3366147
  simp only [CollatzResearch.WordTrace]
  refine ⟨122773467336031785983208695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81848978224021190655472463 122773467336031785983208695)
  ·
    refine ⟨184160201004047678974813043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122773467336031785983208695 184160201004047678974813043)
    ·
      refine ⟨276240301506071518462219565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184160201004047678974813043 276240301506071518462219565)
      ·
        refine ⟨103590113064776819423332337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 276240301506071518462219565 103590113064776819423332337)
        ·
          refine ⟨77692584798582614567499253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103590113064776819423332337 77692584798582614567499253)
          ·
            refine ⟨7283679824867120115703055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77692584798582614567499253 7283679824867120115703055)
            ·
              refine ⟨10925519737300680173554583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7283679824867120115703055 10925519737300680173554583)
              ·
                refine ⟨16388279605951020260331875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10925519737300680173554583 16388279605951020260331875)
                ·
                  refine ⟨24582419408926530390497813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16388279605951020260331875 24582419408926530390497813)
                  ·
                    refine ⟨1152300909793431112054585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24582419408926530390497813 1152300909793431112054585)
                    ·
                      rfl

theorem cell22_3366147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 6].length) (baseStart_3366147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3366147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3366147 prefixEnd_3366147 := by exact prefixLift 3366147
  have htrace : WordTrace (prefixWord ++ tailWord_3366147) baseStart_3366147 baseEnd_3366147 := by
    simpa [prefixWord, tailWord_3366147, baseEnd_3366147] using wordTrace_append hprefix tailTrace_3366147
  have hstable : (prefixWord ++ tailWord_3366147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366147).length < 2 ^ (prefixWord ++ tailWord_3366147).sum := by decide
  have hdescent : baseEnd_3366147 < baseStart_3366147 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366207 : List Nat := [1, 1, 2, 2, 4, 2, 1, 2, 7]
def baseStart_3366207 : Nat := 118140960795 + 3366207 * 2 ^ 59
def prefixEnd_3366207 : Nat := 4983230072969 + 3 ^ 40 * 3366207 * 2
def baseEnd_3366207 : Nat := 384107149673203651851467

theorem tailTrace_3366207 : CollatzResearch.WordTrace tailWord_3366207 prefixEnd_3366207 384107149673203651851467 := by
  unfold tailWord_3366207
  simp only [CollatzResearch.WordTrace]
  refine ⟨122775655715814416230392875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81850437143876277486928583 122775655715814416230392875)
  ·
    refine ⟨184163483573721624345589313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122775655715814416230392875 184163483573721624345589313)
    ·
      refine ⟨138122612680291218259191985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184163483573721624345589313 138122612680291218259191985)
      ·
        refine ⟨103591959510218413694393989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138122612680291218259191985 103591959510218413694393989)
        ·
          refine ⟨19423492408165952567698873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103591959510218413694393989 19423492408165952567698873)
          ·
            refine ⟨14567619306124464425774155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19423492408165952567698873 14567619306124464425774155)
            ·
              refine ⟨21851428959186696638661233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14567619306124464425774155 21851428959186696638661233)
              ·
                refine ⟨16388571719390022478995925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21851428959186696638661233 16388571719390022478995925)
                ·
                  refine ⟨384107149673203651851467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16388571719390022478995925 384107149673203651851467)
                  ·
                    rfl

theorem cell22_3366207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 7].length) (baseStart_3366207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3366207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3366207 prefixEnd_3366207 := by exact prefixLift 3366207
  have htrace : WordTrace (prefixWord ++ tailWord_3366207) baseStart_3366207 baseEnd_3366207 := by
    simpa [prefixWord, tailWord_3366207, baseEnd_3366207] using wordTrace_append hprefix tailTrace_3366207
  have hstable : (prefixWord ++ tailWord_3366207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366207).length < 2 ^ (prefixWord ++ tailWord_3366207).sum := by decide
  have hdescent : baseEnd_3366207 < baseStart_3366207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366230 : List Nat := [5, 2, 3, 1, 1, 1, 2, 7]
def baseStart_3366230 : Nat := 118140960795 + 3366230 * 2 ^ 59
def prefixEnd_3366230 : Nat := 4983230072969 + 3 ^ 40 * 3366230 * 2
def baseEnd_3366230 : Nat := 128036591376627395803259

theorem tailTrace_3366230 : CollatzResearch.WordTrace tailWord_3366230 prefixEnd_3366230 128036591376627395803259 := by
  unfold tailWord_3366230
  simp only [CollatzResearch.WordTrace]
  refine ⟨7673530912170693197405009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81850996396487394105653429 7673530912170693197405009)
  ·
    refine ⟨5755148184128019898053757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7673530912170693197405009 5755148184128019898053757)
    ·
      refine ⟨2158180569048007461770159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5755148184128019898053757 2158180569048007461770159)
      ·
        refine ⟨3237270853572011192655239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2158180569048007461770159 3237270853572011192655239)
        ·
          refine ⟨4855906280358016788982859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3237270853572011192655239 4855906280358016788982859)
          ·
            refine ⟨7283859420537025183474289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4855906280358016788982859 7283859420537025183474289)
            ·
              refine ⟨5462894565402768887605717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7283859420537025183474289 5462894565402768887605717)
              ·
                refine ⟨128036591376627395803259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5462894565402768887605717 128036591376627395803259)
                ·
                  rfl

theorem cell22_3366230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 7].length) (baseStart_3366230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3366230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3366230 prefixEnd_3366230 := by exact prefixLift 3366230
  have htrace : WordTrace (prefixWord ++ tailWord_3366230) baseStart_3366230 baseEnd_3366230 := by
    simpa [prefixWord, tailWord_3366230, baseEnd_3366230] using wordTrace_append hprefix tailTrace_3366230
  have hstable : (prefixWord ++ tailWord_3366230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366230).length < 2 ^ (prefixWord ++ tailWord_3366230).sum := by decide
  have hdescent : baseEnd_3366230 < baseStart_3366230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366301 : List Nat := [1, 4, 2, 1, 3, 2, 2, 1, 1, 5]
def baseStart_3366301 : Nat := 118140960795 + 3366301 * 2 ^ 59
def prefixEnd_3366301 : Nat := 4983230072969 + 3 ^ 40 * 3366301 * 2
def baseEnd_3366301 : Nat := 1152353627140626043704113

theorem tailTrace_3366301 : CollatzResearch.WordTrace tailWord_3366301 prefixEnd_3366301 1152353627140626043704113 := by
  unfold tailWord_3366301
  simp only [CollatzResearch.WordTrace]
  refine ⟨122779084177473870284314757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81852722784982580189543171 122779084177473870284314757)
  ·
    refine ⟨23021078283276350678309017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122779084177473870284314757 23021078283276350678309017)
    ·
      refine ⟨17265808712457263008731763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23021078283276350678309017 17265808712457263008731763)
      ·
        refine ⟨25898713068685894513097645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17265808712457263008731763 25898713068685894513097645)
        ·
          refine ⟨9712017400757210442411617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25898713068685894513097645 9712017400757210442411617)
          ·
            refine ⟨7284013050567907831808713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9712017400757210442411617 7284013050567907831808713)
            ·
              refine ⟨5463009787925930873856535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7284013050567907831808713 5463009787925930873856535)
              ·
                refine ⟨8194514681888896310784803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5463009787925930873856535 8194514681888896310784803)
                ·
                  refine ⟨12291772022833344466177205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8194514681888896310784803 12291772022833344466177205)
                  ·
                    refine ⟨1152353627140626043704113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12291772022833344466177205 1152353627140626043704113)
                    ·
                      rfl

theorem cell22_3366301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_3366301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3366301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3366301 prefixEnd_3366301 := by exact prefixLift 3366301
  have htrace : WordTrace (prefixWord ++ tailWord_3366301) baseStart_3366301 baseEnd_3366301 := by
    simpa [prefixWord, tailWord_3366301, baseEnd_3366301] using wordTrace_append hprefix tailTrace_3366301
  have hstable : (prefixWord ++ tailWord_3366301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366301).length < 2 ^ (prefixWord ++ tailWord_3366301).sum := by decide
  have hdescent : baseEnd_3366301 < baseStart_3366301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366346 : List Nat := [3, 1, 2, 1, 2, 3, 1, 3, 3, 3]
def baseStart_3366346 : Nat := 118140960795 + 3366346 * 2 ^ 59
def prefixEnd_3366346 : Nat := 4983230072969 + 3 ^ 40 * 3366346 * 2
def baseEnd_3366346 : Nat := 1152369031560260926328975

theorem tailTrace_3366346 : CollatzResearch.WordTrace tailWord_3366346 prefixEnd_3366346 1152369031560260926328975 := by
  unfold tailWord_3366346
  simp only [CollatzResearch.WordTrace]
  refine ⟨30695181365577710742425723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81853816974873895313135261 30695181365577710742425723)
  ·
    refine ⟨46042772048366566113638585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30695181365577710742425723 46042772048366566113638585)
    ·
      refine ⟨34532079036274924585228939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46042772048366566113638585 34532079036274924585228939)
      ·
        refine ⟨51798118554412386877843409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34532079036274924585228939 51798118554412386877843409)
        ·
          refine ⟨38848588915809290158382557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51798118554412386877843409 38848588915809290158382557)
          ·
            refine ⟨14568220843428483809393459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38848588915809290158382557 14568220843428483809393459)
            ·
              refine ⟨21852331265142725714090189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14568220843428483809393459 21852331265142725714090189)
              ·
                refine ⟨8194624224428522142783821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21852331265142725714090189 8194624224428522142783821)
                ·
                  refine ⟨3072984084160695803543933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8194624224428522142783821 3072984084160695803543933)
                  ·
                    refine ⟨1152369031560260926328975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3072984084160695803543933 1152369031560260926328975)
                    ·
                      rfl

theorem cell22_3366346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 3, 3, 3].length) (baseStart_3366346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3366346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3366346 prefixEnd_3366346 := by exact prefixLift 3366346
  have htrace : WordTrace (prefixWord ++ tailWord_3366346) baseStart_3366346 baseEnd_3366346 := by
    simpa [prefixWord, tailWord_3366346, baseEnd_3366346] using wordTrace_append hprefix tailTrace_3366346
  have hstable : (prefixWord ++ tailWord_3366346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366346).length < 2 ^ (prefixWord ++ tailWord_3366346).sum := by decide
  have hdescent : baseEnd_3366346 < baseStart_3366346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366359 : List Nat := [1, 1, 3, 2, 1, 1, 1, 7, 5]
def baseStart_3366359 : Nat := 118140960795 + 3366359 * 2 ^ 59
def prefixEnd_3366359 : Nat := 4983230072969 + 3 ^ 40 * 3366359 * 2
def baseEnd_3366359 : Nat := 384124493908644408584645

theorem tailTrace_3366359 : CollatzResearch.WordTrace tailWord_3366359 prefixEnd_3366359 384124493908644408584645 := by
  unfold tailWord_3366359
  simp only [CollatzResearch.WordTrace]
  refine ⟨122781199611263746189926131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81854133074175830793284087 122781199611263746189926131)
  ·
    refine ⟨184171799416895619284889197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122781199611263746189926131 184171799416895619284889197)
    ·
      refine ⟨69064424781335857231833449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184171799416895619284889197 69064424781335857231833449)
      ·
        refine ⟨51798318586001892923875087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69064424781335857231833449 51798318586001892923875087)
        ·
          refine ⟨77697477879002839385812631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51798318586001892923875087 77697477879002839385812631)
          ·
            refine ⟨116546216818504259078718947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77697477879002839385812631 116546216818504259078718947)
            ·
              refine ⟨174819325227756388618078421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116546216818504259078718947 174819325227756388618078421)
              ·
                refine ⟨4097327935025540358236213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 174819325227756388618078421 4097327935025540358236213)
                ·
                  refine ⟨384124493908644408584645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4097327935025540358236213 384124493908644408584645)
                  ·
                    rfl

theorem cell22_3366359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 7, 5].length) (baseStart_3366359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3366359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3366359 prefixEnd_3366359 := by exact prefixLift 3366359
  have htrace : WordTrace (prefixWord ++ tailWord_3366359) baseStart_3366359 baseEnd_3366359 := by
    simpa [prefixWord, tailWord_3366359, baseEnd_3366359] using wordTrace_append hprefix tailTrace_3366359
  have hstable : (prefixWord ++ tailWord_3366359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366359).length < 2 ^ (prefixWord ++ tailWord_3366359).sum := by decide
  have hdescent : baseEnd_3366359 < baseStart_3366359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366451 : List Nat := [1, 1, 1, 2, 4, 3, 2, 2, 2, 4]
def baseStart_3366451 : Nat := 118140960795 + 3366451 * 2 ^ 59
def prefixEnd_3366451 : Nat := 4983230072969 + 3 ^ 40 * 3366451 * 2
def baseEnd_3366451 : Nat := 1152404975206075652453653

theorem tailTrace_3366451 : CollatzResearch.WordTrace tailWord_3366451 prefixEnd_3366451 1152404975206075652453653 := by
  unfold tailWord_3366451
  simp only [CollatzResearch.WordTrace]
  refine ⟨122784555126930445902275207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81856370084620297268183471 122784555126930445902275207)
  ·
    refine ⟨184176832690395668853412811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122784555126930445902275207 184176832690395668853412811)
    ·
      refine ⟨276265249035593503280119217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184176832690395668853412811 276265249035593503280119217)
      ·
        refine ⟨207198936776695127460089413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276265249035593503280119217 207198936776695127460089413)
        ·
          refine ⟨38849800645630336398766765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 207198936776695127460089413 38849800645630336398766765)
          ·
            refine ⟨14568675242111376149537537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38849800645630336398766765 14568675242111376149537537)
            ·
              refine ⟨10926506431583532112153153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14568675242111376149537537 10926506431583532112153153)
              ·
                refine ⟨8194879823687649084114865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10926506431583532112153153 8194879823687649084114865)
                ·
                  refine ⟨6146159867765736813086149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8194879823687649084114865 6146159867765736813086149)
                  ·
                    refine ⟨1152404975206075652453653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6146159867765736813086149 1152404975206075652453653)
                    ·
                      rfl

theorem cell22_3366451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 2, 2, 4].length) (baseStart_3366451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3366451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3366451 prefixEnd_3366451 := by exact prefixLift 3366451
  have htrace : WordTrace (prefixWord ++ tailWord_3366451) baseStart_3366451 baseEnd_3366451 := by
    simpa [prefixWord, tailWord_3366451, baseEnd_3366451] using wordTrace_append hprefix tailTrace_3366451
  have hstable : (prefixWord ++ tailWord_3366451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366451).length < 2 ^ (prefixWord ++ tailWord_3366451).sum := by decide
  have hdescent : baseEnd_3366451 < baseStart_3366451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366453 : List Nat := [1, 3, 3, 1, 1, 3, 1, 4, 2, 3]
def baseStart_3366453 : Nat := 118140960795 + 3366453 * 2 ^ 59
def prefixEnd_3366453 : Nat := 4983230072969 + 3 ^ 40 * 3366453 * 2
def baseEnd_3366453 : Nat := 1152405659846948313903647

theorem tailTrace_3366453 : CollatzResearch.WordTrace tailWord_3366453 prefixEnd_3366453 1152405659846948313903647 := by
  unfold tailWord_3366453
  simp only [CollatzResearch.WordTrace]
  refine ⟨122784628072923200243848013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81856418715282133495898675 122784628072923200243848013)
  ·
    refine ⟨46044235527346200091443005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122784628072923200243848013 46044235527346200091443005)
    ·
      refine ⟨17266588322754825034291127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46044235527346200091443005 17266588322754825034291127)
      ·
        refine ⟨25899882484132237551436691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17266588322754825034291127 25899882484132237551436691)
        ·
          refine ⟨38849823726198356327155037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25899882484132237551436691 38849823726198356327155037)
          ·
            refine ⟨14568683897324383622683139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38849823726198356327155037 14568683897324383622683139)
            ·
              refine ⟨21853025845986575434024709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14568683897324383622683139 21853025845986575434024709)
              ·
                refine ⟨4097442346122482893879633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21853025845986575434024709 4097442346122482893879633)
                ·
                  refine ⟨3073081759591862170409725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4097442346122482893879633 3073081759591862170409725)
                  ·
                    refine ⟨1152405659846948313903647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3073081759591862170409725 1152405659846948313903647)
                    ·
                      rfl

theorem cell22_3366453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_3366453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3366453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3366453 prefixEnd_3366453 := by exact prefixLift 3366453
  have htrace : WordTrace (prefixWord ++ tailWord_3366453) baseStart_3366453 baseEnd_3366453 := by
    simpa [prefixWord, tailWord_3366453, baseEnd_3366453] using wordTrace_append hprefix tailTrace_3366453
  have hstable : (prefixWord ++ tailWord_3366453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366453).length < 2 ^ (prefixWord ++ tailWord_3366453).sum := by decide
  have hdescent : baseEnd_3366453 < baseStart_3366453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366455 : List Nat := [1, 1, 3, 1, 2, 6, 2, 2, 4]
def baseStart_3366455 : Nat := 118140960795 + 3366455 * 2 ^ 59
def prefixEnd_3366455 : Nat := 4983230072969 + 3 ^ 40 * 3366455 * 2
def baseEnd_3366455 : Nat := 384135448162606991784547

theorem tailTrace_3366455 : CollatzResearch.WordTrace tailWord_3366455 prefixEnd_3366455 384135448162606991784547 := by
  unfold tailWord_3366455
  simp only [CollatzResearch.WordTrace]
  refine ⟨122784701018915954585420819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81856467345943969723613879 122784701018915954585420819)
  ·
    refine ⟨184177051528373931878131229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122784701018915954585420819 184177051528373931878131229)
    ·
      refine ⟨69066394323140224454299211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184177051528373931878131229 69066394323140224454299211)
      ·
        refine ⟨103599591484710336681448817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69066394323140224454299211 103599591484710336681448817)
        ·
          refine ⟨77699693613532752511086613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103599591484710336681448817 77699693613532752511086613)
          ·
            refine ⟨3642173138134347773957185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 77699693613532752511086613 3642173138134347773957185)
            ·
              refine ⟨2731629853600760830467889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3642173138134347773957185 2731629853600760830467889)
              ·
                refine ⟨2048722390200570622850917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2731629853600760830467889 2048722390200570622850917)
                ·
                  refine ⟨384135448162606991784547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2048722390200570622850917 384135448162606991784547)
                  ·
                    rfl

theorem cell22_3366455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2, 2, 4].length) (baseStart_3366455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3366455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3366455 prefixEnd_3366455 := by exact prefixLift 3366455
  have htrace : WordTrace (prefixWord ++ tailWord_3366455) baseStart_3366455 baseEnd_3366455 := by
    simpa [prefixWord, tailWord_3366455, baseEnd_3366455] using wordTrace_append hprefix tailTrace_3366455
  have hstable : (prefixWord ++ tailWord_3366455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366455).length < 2 ^ (prefixWord ++ tailWord_3366455).sum := by decide
  have hdescent : baseEnd_3366455 < baseStart_3366455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366464 : List Nat := [2, 1, 1, 2, 2, 2, 1, 2, 2, 7]
def baseStart_3366464 : Nat := 118140960795 + 3366464 * 2 ^ 59
def prefixEnd_3366464 : Nat := 4983230072969 + 3 ^ 40 * 3366464 * 2
def baseEnd_3366464 : Nat := 1152409425371747951878613

theorem tailTrace_3366464 : CollatzResearch.WordTrace tailWord_3366464 prefixEnd_3366464 1152409425371747951878613 := by
  unfold tailWord_3366464
  simp only [CollatzResearch.WordTrace]
  refine ⟨61392514637941674561249223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81856686183922232748332297 61392514637941674561249223)
  ·
    refine ⟨92088771956912511841873835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61392514637941674561249223 92088771956912511841873835)
    ·
      refine ⟨138133157935368767762810753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92088771956912511841873835 138133157935368767762810753)
      ·
        refine ⟨103599868451526575822108065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138133157935368767762810753 103599868451526575822108065)
        ·
          refine ⟨77699901338644931866581049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103599868451526575822108065 77699901338644931866581049)
          ·
            refine ⟨58274926003983698899935787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77699901338644931866581049 58274926003983698899935787)
            ·
              refine ⟨87412389005975548349903681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58274926003983698899935787 87412389005975548349903681)
              ·
                refine ⟨65559291754481661262427761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87412389005975548349903681 65559291754481661262427761)
                ·
                  refine ⟨49169468815861245946820821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65559291754481661262427761 49169468815861245946820821)
                  ·
                    refine ⟨1152409425371747951878613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49169468815861245946820821 1152409425371747951878613)
                    ·
                      rfl

theorem cell22_3366464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 2, 7].length) (baseStart_3366464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3366464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3366464 prefixEnd_3366464 := by exact prefixLift 3366464
  have htrace : WordTrace (prefixWord ++ tailWord_3366464) baseStart_3366464 baseEnd_3366464 := by
    simpa [prefixWord, tailWord_3366464, baseEnd_3366464] using wordTrace_append hprefix tailTrace_3366464
  have hstable : (prefixWord ++ tailWord_3366464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366464).length < 2 ^ (prefixWord ++ tailWord_3366464).sum := by decide
  have hdescent : baseEnd_3366464 < baseStart_3366464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366479 : List Nat := [1, 1, 2, 1, 1, 2, 3, 1, 4, 6]
def baseStart_3366479 : Nat := 118140960795 + 3366479 * 2 ^ 59
def prefixEnd_3366479 : Nat := 4983230072969 + 3 ^ 40 * 3366479 * 2
def baseEnd_3366479 : Nat := 1152414560178292912753567

theorem tailTrace_3366479 : CollatzResearch.WordTrace tailWord_3366479 prefixEnd_3366479 1152414560178292912753567 := by
  unfold tailWord_3366479
  simp only [CollatzResearch.WordTrace]
  refine ⟨122785576370829006684294491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81857050913886004456196327 122785576370829006684294491)
  ·
    refine ⟨184178364556243510026441737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122785576370829006684294491 184178364556243510026441737)
    ·
      refine ⟨138133773417182632519831303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184178364556243510026441737 138133773417182632519831303)
      ·
        refine ⟨207200660125773948779746955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138133773417182632519831303 207200660125773948779746955)
        ·
          refine ⟨310800990188660923169620433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207200660125773948779746955 310800990188660923169620433)
          ·
            refine ⟨233100742641495692377215325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 310800990188660923169620433 233100742641495692377215325)
            ·
              refine ⟨87412778490560884641455747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 233100742641495692377215325 87412778490560884641455747)
              ·
                refine ⟨131119167735841326962183621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87412778490560884641455747 131119167735841326962183621)
                ·
                  refine ⟨24584843950470248805409429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 131119167735841326962183621 24584843950470248805409429)
                  ·
                    refine ⟨1152414560178292912753567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24584843950470248805409429 1152414560178292912753567)
                    ·
                      rfl

theorem cell22_3366479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 6].length) (baseStart_3366479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3366479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3366479 prefixEnd_3366479 := by exact prefixLift 3366479
  have htrace : WordTrace (prefixWord ++ tailWord_3366479) baseStart_3366479 baseEnd_3366479 := by
    simpa [prefixWord, tailWord_3366479, baseEnd_3366479] using wordTrace_append hprefix tailTrace_3366479
  have hstable : (prefixWord ++ tailWord_3366479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366479).length < 2 ^ (prefixWord ++ tailWord_3366479).sum := by decide
  have hdescent : baseEnd_3366479 < baseStart_3366479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366528 : List Nat := [2, 1, 1, 2, 1, 4, 5, 1, 5]
def baseStart_3366528 : Nat := 118140960795 + 3366528 * 2 ^ 59
def prefixEnd_3366528 : Nat := 4983230072969 + 3 ^ 40 * 3366528 * 2
def baseEnd_3366528 : Nat := 384143777959891039426139

theorem tailTrace_3366528 : CollatzResearch.WordTrace tailWord_3366528 prefixEnd_3366528 384143777959891039426139 := by
  unfold tailWord_3366528
  simp only [CollatzResearch.WordTrace]
  refine ⟨61393681773825744026414119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81858242365100992035218825 61393681773825744026414119)
  ·
    refine ⟨92090522660738616039621179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61393681773825744026414119 92090522660738616039621179)
    ·
      refine ⟨138135783991107924059431769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92090522660738616039621179 138135783991107924059431769)
      ·
        refine ⟨103601837993330943044573827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138135783991107924059431769 103601837993330943044573827)
        ·
          refine ⟨155402756989996414566860741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103601837993330943044573827 155402756989996414566860741)
          ·
            refine ⟨29138016935624327731286389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155402756989996414566860741 29138016935624327731286389)
            ·
              refine ⟨2731689087714780724808099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29138016935624327731286389 2731689087714780724808099)
              ·
                refine ⟨4097533631572171087212149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2731689087714780724808099 4097533631572171087212149)
                ·
                  refine ⟨384143777959891039426139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4097533631572171087212149 384143777959891039426139)
                  ·
                    rfl

theorem cell22_3366528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5, 1, 5].length) (baseStart_3366528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3366528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3366528 prefixEnd_3366528 := by exact prefixLift 3366528
  have htrace : WordTrace (prefixWord ++ tailWord_3366528) baseStart_3366528 baseEnd_3366528 := by
    simpa [prefixWord, tailWord_3366528, baseEnd_3366528] using wordTrace_append hprefix tailTrace_3366528
  have hstable : (prefixWord ++ tailWord_3366528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366528).length < 2 ^ (prefixWord ++ tailWord_3366528).sum := by decide
  have hdescent : baseEnd_3366528 < baseStart_3366528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366605 : List Nat := [1, 6, 2, 1, 1, 1, 1, 1, 3, 5]
def baseStart_3366605 : Nat := 118140960795 + 3366605 * 2 ^ 59
def prefixEnd_3366605 : Nat := 4983230072969 + 3 ^ 40 * 3366605 * 2
def baseEnd_3366605 : Nat := 1152457692553270584103181

theorem tailTrace_3366605 : CollatzResearch.WordTrace tailWord_3366605 prefixEnd_3366605 1152457692553270584103181 := by
  unfold tailWord_3366605
  simp only [CollatzResearch.WordTrace]
  refine ⟨122790171968372530203381269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81860114645581686802254179 122790171968372530203381269)
  ·
    refine ⟨5755789311017462353283497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 122790171968372530203381269 5755789311017462353283497)
    ·
      refine ⟨4316841983263096764962623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5755789311017462353283497 4316841983263096764962623)
      ·
        refine ⟨6475262974894645147443935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4316841983263096764962623 6475262974894645147443935)
        ·
          refine ⟨9712894462341967721165903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6475262974894645147443935 9712894462341967721165903)
          ·
            refine ⟨14569341693512951581748855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9712894462341967721165903 14569341693512951581748855)
            ·
              refine ⟨21854012540269427372623283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14569341693512951581748855 21854012540269427372623283)
              ·
                refine ⟨32781018810404141058934925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21854012540269427372623283 32781018810404141058934925)
                ·
                  refine ⟨12292882053901552897100597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32781018810404141058934925 12292882053901552897100597)
                  ·
                    refine ⟨1152457692553270584103181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12292882053901552897100597 1152457692553270584103181)
                    ·
                      rfl

theorem cell22_3366605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_3366605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3366605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3366605 prefixEnd_3366605 := by exact prefixLift 3366605
  have htrace : WordTrace (prefixWord ++ tailWord_3366605) baseStart_3366605 baseEnd_3366605 := by
    simpa [prefixWord, tailWord_3366605, baseEnd_3366605] using wordTrace_append hprefix tailTrace_3366605
  have hstable : (prefixWord ++ tailWord_3366605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366605).length < 2 ^ (prefixWord ++ tailWord_3366605).sum := by decide
  have hdescent : baseEnd_3366605 < baseStart_3366605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366633 : List Nat := [1, 2, 1, 1, 1, 2, 3, 5, 3, 3]
def baseStart_3366633 : Nat := 118140960795 + 3366633 * 2 ^ 59
def prefixEnd_3366633 : Nat := 4983230072969 + 3 ^ 40 * 3366633 * 2
def baseEnd_3366633 : Nat := 1152467277525487844403095

theorem tailTrace_3366633 : CollatzResearch.WordTrace tailWord_3366633 prefixEnd_3366633 1152467277525487844403095 := by
  unfold tailWord_3366633
  simp only [CollatzResearch.WordTrace]
  refine ⟨122791193212271090985400553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81860795474847393990267035 122791193212271090985400553)
  ·
    refine ⟨92093394909203318239050415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122791193212271090985400553 92093394909203318239050415)
    ·
      refine ⟨138140092363804977358575623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92093394909203318239050415 138140092363804977358575623)
      ·
        refine ⟨207210138545707466037863435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138140092363804977358575623 207210138545707466037863435)
        ·
          refine ⟨310815207818561199056795153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207210138545707466037863435 310815207818561199056795153)
          ·
            refine ⟨233111405863920899292596365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 310815207818561199056795153 233111405863920899292596365)
            ·
              refine ⟨87416777198970337234723637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 233111405863920899292596365 87416777198970337234723637)
              ·
                refine ⟨8195322862403469115755341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87416777198970337234723637 8195322862403469115755341)
                ·
                  refine ⟨3073246073401300918408253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8195322862403469115755341 3073246073401300918408253)
                  ·
                    refine ⟨1152467277525487844403095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3073246073401300918408253 1152467277525487844403095)
                    ·
                      rfl

theorem cell22_3366633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5, 3, 3].length) (baseStart_3366633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3366633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3366633 prefixEnd_3366633 := by exact prefixLift 3366633
  have htrace : WordTrace (prefixWord ++ tailWord_3366633) baseStart_3366633 baseEnd_3366633 := by
    simpa [prefixWord, tailWord_3366633, baseEnd_3366633] using wordTrace_append hprefix tailTrace_3366633
  have hstable : (prefixWord ++ tailWord_3366633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366633).length < 2 ^ (prefixWord ++ tailWord_3366633).sum := by decide
  have hdescent : baseEnd_3366633 < baseStart_3366633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366654 : List Nat := [4, 2, 2, 1, 4, 1, 1, 1, 2, 4]
def baseStart_3366654 : Nat := 118140960795 + 3366654 * 2 ^ 59
def prefixEnd_3366654 : Nat := 4983230072969 + 3 ^ 40 * 3366654 * 2
def baseEnd_3366654 : Nat := 1152474466254650789628031

theorem tailTrace_3366654 : CollatzResearch.WordTrace tailWord_3366654 prefixEnd_3366654 1152474466254650789628031 := by
  unfold tailWord_3366654
  simp only [CollatzResearch.WordTrace]
  refine ⟨15348994893149376446489377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81861306096796674381276677 15348994893149376446489377)
  ·
    refine ⟨11511746169862032334867033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15348994893149376446489377 11511746169862032334867033)
    ·
      refine ⟨8633809627396524251150275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11511746169862032334867033 8633809627396524251150275)
      ·
        refine ⟨12950714441094786376725413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8633809627396524251150275 12950714441094786376725413)
        ·
          refine ⟨2428258957705272445636015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12950714441094786376725413 2428258957705272445636015)
          ·
            refine ⟨3642388436557908668454023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2428258957705272445636015 3642388436557908668454023)
            ·
              refine ⟨5463582654836863002681035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3642388436557908668454023 5463582654836863002681035)
              ·
                refine ⟨8195373982255294504021553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5463582654836863002681035 8195373982255294504021553)
                ·
                  refine ⟨6146530486691470878016165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8195373982255294504021553 6146530486691470878016165)
                  ·
                    refine ⟨1152474466254650789628031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6146530486691470878016165 1152474466254650789628031)
                    ·
                      rfl

theorem cell22_3366654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_3366654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3366654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3366654 prefixEnd_3366654 := by exact prefixLift 3366654
  have htrace : WordTrace (prefixWord ++ tailWord_3366654) baseStart_3366654 baseEnd_3366654 := by
    simpa [prefixWord, tailWord_3366654, baseEnd_3366654] using wordTrace_append hprefix tailTrace_3366654
  have hstable : (prefixWord ++ tailWord_3366654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366654).length < 2 ^ (prefixWord ++ tailWord_3366654).sum := by decide
  have hdescent : baseEnd_3366654 < baseStart_3366654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366669 : List Nat := [1, 7, 2, 1, 1, 1, 9]
def baseStart_3366669 : Nat := 118140960795 + 3366669 * 2 ^ 59
def prefixEnd_3366669 : Nat := 4983230072969 + 3 ^ 40 * 3366669 * 2
def baseEnd_3366669 : Nat := 42684429668933175944555

theorem tailTrace_3366669 : CollatzResearch.WordTrace tailWord_3366669 prefixEnd_3366669 42684429668933175944555 := by
  unfold tailWord_3366669
  simp only [CollatzResearch.WordTrace]
  refine ⟨122792506240140669133711061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81861670826760446089140707 122792506240140669133711061)
  ·
    refine ⟨2877949365003296932821353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 122792506240140669133711061 2877949365003296932821353)
    ·
      refine ⟨2158462023752472699616015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2877949365003296932821353 2158462023752472699616015)
      ·
        refine ⟨3237693035628709049424023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2158462023752472699616015 3237693035628709049424023)
        ·
          refine ⟨4856539553443063574136035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3237693035628709049424023 4856539553443063574136035)
          ·
            refine ⟨7284809330164595361204053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4856539553443063574136035 7284809330164595361204053)
            ·
              refine ⟨42684429668933175944555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7284809330164595361204053 42684429668933175944555)
              ·
                rfl

theorem cell22_3366669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 9].length) (baseStart_3366669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3366669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3366669 prefixEnd_3366669 := by exact prefixLift 3366669
  have htrace : WordTrace (prefixWord ++ tailWord_3366669) baseStart_3366669 baseEnd_3366669 := by
    simpa [prefixWord, tailWord_3366669, baseEnd_3366669] using wordTrace_append hprefix tailTrace_3366669
  have hstable : (prefixWord ++ tailWord_3366669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366669).length < 2 ^ (prefixWord ++ tailWord_3366669).sum := by decide
  have hdescent : baseEnd_3366669 < baseStart_3366669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366753 : List Nat := [1, 2, 3, 1, 1, 1, 6, 7]
def baseStart_3366753 : Nat := 118140960795 + 3366753 * 2 ^ 59
def prefixEnd_3366753 : Nat := 4983230072969 + 3 ^ 40 * 3366753 * 2
def baseEnd_3366753 : Nat := 128056483997538614600303

theorem tailTrace_3366753 : CollatzResearch.WordTrace tailWord_3366753 prefixEnd_3366753 128056483997538614600303 := by
  unfold tailWord_3366753
  simp only [CollatzResearch.WordTrace]
  refine ⟨122795569971836351479768913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81863713314557567653179275 122795569971836351479768913)
  ·
    refine ⟨92096677478877263609826685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122795569971836351479768913 92096677478877263609826685)
    ·
      refine ⟨34536254054578973853685007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92096677478877263609826685 34536254054578973853685007)
      ·
        refine ⟨51804381081868460780527511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34536254054578973853685007 51804381081868460780527511)
        ·
          refine ⟨77706571622802691170791267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51804381081868460780527511 77706571622802691170791267)
          ·
            refine ⟨116559857434204036756186901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77706571622802691170791267 116559857434204036756186901)
            ·
              refine ⟨5463743317228314222946261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 116559857434204036756186901 5463743317228314222946261)
              ·
                refine ⟨128056483997538614600303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5463743317228314222946261 128056483997538614600303)
                ·
                  rfl

theorem cell22_3366753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 7].length) (baseStart_3366753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3366753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3366753 prefixEnd_3366753 := by exact prefixLift 3366753
  have htrace : WordTrace (prefixWord ++ tailWord_3366753) baseStart_3366753 baseEnd_3366753 := by
    simpa [prefixWord, tailWord_3366753, baseEnd_3366753] using wordTrace_append hprefix tailTrace_3366753
  have hstable : (prefixWord ++ tailWord_3366753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366753).length < 2 ^ (prefixWord ++ tailWord_3366753).sum := by decide
  have hdescent : baseEnd_3366753 < baseStart_3366753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366860 : List Nat := [2, 2, 1, 4, 1, 2, 1, 3, 6]
def baseStart_3366860 : Nat := 118140960795 + 3366860 * 2 ^ 59
def prefixEnd_3366860 : Nat := 4983230072969 + 3 ^ 40 * 3366860 * 2
def baseEnd_3366860 : Nat := 384181661421511639659133

theorem tailTrace_3366860 : CollatzResearch.WordTrace tailWord_3366860 prefixEnd_3366860 384181661421511639659133 := by
  unfold tailWord_3366860
  simp only [CollatzResearch.WordTrace]
  refine ⟨61399736291224354376957017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81866315054965805835942689 61399736291224354376957017)
  ·
    refine ⟨46049802218418265782717763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61399736291224354376957017 46049802218418265782717763)
    ·
      refine ⟨69074703327627398674076645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46049802218418265782717763 69074703327627398674076645)
      ·
        refine ⟨12951506873930137251389371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69074703327627398674076645 12951506873930137251389371)
        ·
          refine ⟨19427260310895205877084057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12951506873930137251389371 19427260310895205877084057)
          ·
            refine ⟨14570445233171404407813043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19427260310895205877084057 14570445233171404407813043)
            ·
              refine ⟨21855667849757106611719565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14570445233171404407813043 21855667849757106611719565)
              ·
                refine ⟨8195875443658914979394837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21855667849757106611719565 8195875443658914979394837)
                ·
                  refine ⟨384181661421511639659133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8195875443658914979394837 384181661421511639659133)
                  ·
                    rfl

theorem cell22_3366860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 3, 6].length) (baseStart_3366860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3366860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3366860 prefixEnd_3366860 := by exact prefixLift 3366860
  have htrace : WordTrace (prefixWord ++ tailWord_3366860) baseStart_3366860 baseEnd_3366860 := by
    simpa [prefixWord, tailWord_3366860, baseEnd_3366860] using wordTrace_append hprefix tailTrace_3366860
  have hstable : (prefixWord ++ tailWord_3366860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366860).length < 2 ^ (prefixWord ++ tailWord_3366860).sum := by decide
  have hdescent : baseEnd_3366860 < baseStart_3366860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366890 : List Nat := [3, 1, 3, 1, 2, 1, 1, 3, 1, 6]
def baseStart_3366890 : Nat := 118140960795 + 3366890 * 2 ^ 59
def prefixEnd_3366890 : Nat := 4983230072969 + 3 ^ 40 * 3366890 * 2
def baseEnd_3366890 : Nat := 1152555253877624840727307

theorem tailTrace_3366890 : CollatzResearch.WordTrace tailWord_3366890 prefixEnd_3366890 1152555253877624840727307 := by
  unfold tailWord_3366890
  simp only [CollatzResearch.WordTrace]
  refine ⟨30700141693085005969376531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81867044514893349251670749 30700141693085005969376531)
  ·
    refine ⟨46050212539627508954064797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30700141693085005969376531 46050212539627508954064797)
    ·
      refine ⟨17268829702360315857774299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46050212539627508954064797 17268829702360315857774299)
      ·
        refine ⟨25903244553540473786661449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17268829702360315857774299 25903244553540473786661449)
        ·
          refine ⟨19427433415155355339996087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25903244553540473786661449 19427433415155355339996087)
          ·
            refine ⟨29141150122733033009994131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19427433415155355339996087 29141150122733033009994131)
            ·
              refine ⟨43711725184099549514991197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29141150122733033009994131 43711725184099549514991197)
              ·
                refine ⟨16391896944037331068121699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43711725184099549514991197 16391896944037331068121699)
                ·
                  refine ⟨24587845416055996602182549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16391896944037331068121699 24587845416055996602182549)
                  ·
                    refine ⟨1152555253877624840727307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24587845416055996602182549 1152555253877624840727307)
                    ·
                      rfl

theorem cell22_3366890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_3366890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3366890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3366890 prefixEnd_3366890 := by exact prefixLift 3366890
  have htrace : WordTrace (prefixWord ++ tailWord_3366890) baseStart_3366890 baseEnd_3366890 := by
    simpa [prefixWord, tailWord_3366890, baseEnd_3366890] using wordTrace_append hprefix tailTrace_3366890
  have hstable : (prefixWord ++ tailWord_3366890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366890).length < 2 ^ (prefixWord ++ tailWord_3366890).sum := by decide
  have hdescent : baseEnd_3366890 < baseStart_3366890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366894 : List Nat := [4, 1, 2, 1, 3, 1, 3, 3, 4]
def baseStart_3366894 : Nat := 118140960795 + 3366894 * 2 ^ 59
def prefixEnd_3366894 : Nat := 4983230072969 + 3 ^ 40 * 3366894 * 2
def baseEnd_3366894 : Nat := 384185541053123387875765

theorem tailTrace_3366894 : CollatzResearch.WordTrace tailWord_3366894 prefixEnd_3366894 384185541053123387875765 := by
  unfold tailWord_3366894
  simp only [CollatzResearch.WordTrace]
  refine ⟨15350089083040691570081467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81867141776217021707101157 15350089083040691570081467)
  ·
    refine ⟨23025133624561037355122201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15350089083040691570081467 23025133624561037355122201)
    ·
      refine ⟨17268850218420778016341651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23025133624561037355122201 17268850218420778016341651)
      ·
        refine ⟨25903275327631167024512477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17268850218420778016341651 25903275327631167024512477)
        ·
          refine ⟨9713728247861687634192179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25903275327631167024512477 9713728247861687634192179)
          ·
            refine ⟨14570592371792531451288269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9713728247861687634192179 14570592371792531451288269)
            ·
              refine ⟨5463972139422199294233101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14570592371792531451288269 5463972139422199294233101)
              ·
                refine ⟨2048989552283324735337413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5463972139422199294233101 2048989552283324735337413)
                ·
                  refine ⟨384185541053123387875765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2048989552283324735337413 384185541053123387875765)
                  ·
                    rfl

theorem cell22_3366894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 3, 4].length) (baseStart_3366894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3366894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3366894 prefixEnd_3366894 := by exact prefixLift 3366894
  have htrace : WordTrace (prefixWord ++ tailWord_3366894) baseStart_3366894 baseEnd_3366894 := by
    simpa [prefixWord, tailWord_3366894, baseEnd_3366894] using wordTrace_append hprefix tailTrace_3366894
  have hstable : (prefixWord ++ tailWord_3366894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366894).length < 2 ^ (prefixWord ++ tailWord_3366894).sum := by decide
  have hdescent : baseEnd_3366894 < baseStart_3366894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366905 : List Nat := [1, 2, 1, 3, 1, 6, 8]
def baseStart_3366905 : Nat := 118140960795 + 3366905 * 2 ^ 59
def prefixEnd_3366905 : Nat := 4983230072969 + 3 ^ 40 * 3366905 * 2
def baseEnd_3366905 : Nat := 42687421803117400059343

theorem tailTrace_3366905 : CollatzResearch.WordTrace tailWord_3366905 prefixEnd_3366905 42687421803117400059343 := by
  unfold tailWord_3366905
  simp only [CollatzResearch.WordTrace]
  refine ⟨122801113867285681439302169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81867409244857120959534779 122801113867285681439302169)
  ·
    refine ⟨92100835400464261079476627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122801113867285681439302169 92100835400464261079476627)
    ·
      refine ⟨138151253100696391619214941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92100835400464261079476627 138151253100696391619214941)
      ·
        refine ⟨51806719912761146857205603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138151253100696391619214941 51806719912761146857205603)
        ·
          refine ⟨77710079869141720285808405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51806719912761146857205603 77710079869141720285808405)
          ·
            refine ⟨3642659993866018138397269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 77710079869141720285808405 3642659993866018138397269)
            ·
              refine ⟨42687421803117400059343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3642659993866018138397269 42687421803117400059343)
              ·
                rfl

theorem cell22_3366905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 8].length) (baseStart_3366905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3366905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3366905 prefixEnd_3366905 := by exact prefixLift 3366905
  have htrace : WordTrace (prefixWord ++ tailWord_3366905) baseStart_3366905 baseEnd_3366905 := by
    simpa [prefixWord, tailWord_3366905, baseEnd_3366905] using wordTrace_append hprefix tailTrace_3366905
  have hstable : (prefixWord ++ tailWord_3366905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366905).length < 2 ^ (prefixWord ++ tailWord_3366905).sum := by decide
  have hdescent : baseEnd_3366905 < baseStart_3366905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366922 : List Nat := [3, 1, 2, 2, 4, 1, 2, 7]
def baseStart_3366922 : Nat := 118140960795 + 3366922 * 2 ^ 59
def prefixEnd_3366922 : Nat := 4983230072969 + 3 ^ 40 * 3366922 * 2
def baseEnd_3366922 : Nat := 128062912014620824880801

theorem tailTrace_3366922 : CollatzResearch.WordTrace tailWord_3366922 prefixEnd_3366922 128062912014620824880801 := by
  unfold tailWord_3366922
  simp only [CollatzResearch.WordTrace]
  refine ⟨30700433477056023335667755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81867822605482728895114013 30700433477056023335667755)
  ·
    refine ⟨46050650215584035003501633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30700433477056023335667755 46050650215584035003501633)
    ·
      refine ⟨34537987661688026252626225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46050650215584035003501633 34537987661688026252626225)
      ·
        refine ⟨25903490746266019689469669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34537987661688026252626225 25903490746266019689469669)
        ·
          refine ⟨4856904514924878691775563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25903490746266019689469669 4856904514924878691775563)
          ·
            refine ⟨7285356772387318037663345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4856904514924878691775563 7285356772387318037663345)
            ·
              refine ⟨5464017579290488528247509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7285356772387318037663345 5464017579290488528247509)
              ·
                refine ⟨128062912014620824880801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5464017579290488528247509 128062912014620824880801)
                ·
                  rfl

theorem cell22_3366922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 7].length) (baseStart_3366922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3366922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3366922 prefixEnd_3366922 := by exact prefixLift 3366922
  have htrace : WordTrace (prefixWord ++ tailWord_3366922) baseStart_3366922 baseEnd_3366922 := by
    simpa [prefixWord, tailWord_3366922, baseEnd_3366922] using wordTrace_append hprefix tailTrace_3366922
  have hstable : (prefixWord ++ tailWord_3366922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366922).length < 2 ^ (prefixWord ++ tailWord_3366922).sum := by decide
  have hdescent : baseEnd_3366922 < baseStart_3366922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366997 : List Nat := [1, 3, 2, 2, 1, 3, 2, 1, 3, 4]
def baseStart_3366997 : Nat := 118140960795 + 3366997 * 2 ^ 59
def prefixEnd_3366997 : Nat := 4983230072969 + 3 ^ 40 * 3366997 * 2
def baseEnd_3366997 : Nat := 1152591882164312228301979

theorem tailTrace_3366997 : CollatzResearch.WordTrace tailWord_3366997 prefixEnd_3366997 1152591882164312228301979 := by
  unfold tailWord_3366997
  simp only [CollatzResearch.WordTrace]
  refine ⟨122804469382952381151651245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81869646255301587434434163 122804469382952381151651245)
  ·
    refine ⟨46051676018607142931869217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122804469382952381151651245 46051676018607142931869217)
    ·
      refine ⟨34538757013955357198901913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46051676018607142931869217 34538757013955357198901913)
      ·
        refine ⟨25904067760466517899176435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34538757013955357198901913 25904067760466517899176435)
        ·
          refine ⟨38856101640699776848764653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25904067760466517899176435 38856101640699776848764653)
          ·
            refine ⟨14571038115262416318286745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38856101640699776848764653 14571038115262416318286745)
            ·
              refine ⟨10928278586446812238715059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14571038115262416318286745 10928278586446812238715059)
              ·
                refine ⟨16392417879670218358072589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10928278586446812238715059 16392417879670218358072589)
                ·
                  refine ⟨6147156704876331884277221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16392417879670218358072589 6147156704876331884277221)
                  ·
                    refine ⟨1152591882164312228301979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6147156704876331884277221 1152591882164312228301979)
                    ·
                      rfl

theorem cell22_3366997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_3366997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3366997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3366997 prefixEnd_3366997 := by exact prefixLift 3366997
  have htrace : WordTrace (prefixWord ++ tailWord_3366997) baseStart_3366997 baseEnd_3366997 := by
    simpa [prefixWord, tailWord_3366997, baseEnd_3366997] using wordTrace_append hprefix tailTrace_3366997
  have hstable : (prefixWord ++ tailWord_3366997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366997).length < 2 ^ (prefixWord ++ tailWord_3366997).sum := by decide
  have hdescent : baseEnd_3366997 < baseStart_3366997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367040 : List Nat := [2, 1, 1, 2, 1, 3, 1, 11]
def baseStart_3367040 : Nat := 118140960795 + 3367040 * 2 ^ 59
def prefixEnd_3367040 : Nat := 4983230072969 + 3 ^ 40 * 3367040 * 2
def baseEnd_3367040 : Nat := 128067400215897161052983

theorem tailTrace_3367040 : CollatzResearch.WordTrace tailWord_3367040 prefixEnd_3367040 128067400215897161052983 := by
  unfold tailWord_3367040
  simp only [CollatzResearch.WordTrace]
  refine ⟨61403018860898299747733287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81870691814531066330311049 61403018860898299747733287)
  ·
    refine ⟨92104528291347449621599931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61403018860898299747733287 92104528291347449621599931)
    ·
      refine ⟨138156792437021174432399897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92104528291347449621599931 138156792437021174432399897)
      ·
        refine ⟨103617594327765880824299923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138156792437021174432399897 103617594327765880824299923)
        ·
          refine ⟨155426391491648821236449885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103617594327765880824299923 155426391491648821236449885)
          ·
            refine ⟨58284896809368307963668707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155426391491648821236449885 58284896809368307963668707)
            ·
              refine ⟨87427345214052461945503061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58284896809368307963668707 87427345214052461945503061)
              ·
                refine ⟨128067400215897161052983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 87427345214052461945503061 128067400215897161052983)
                ·
                  rfl

theorem cell22_3367040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 11].length) (baseStart_3367040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3367040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3367040 prefixEnd_3367040 := by exact prefixLift 3367040
  have htrace : WordTrace (prefixWord ++ tailWord_3367040) baseStart_3367040 baseEnd_3367040 := by
    simpa [prefixWord, tailWord_3367040, baseEnd_3367040] using wordTrace_append hprefix tailTrace_3367040
  have hstable : (prefixWord ++ tailWord_3367040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367040).length < 2 ^ (prefixWord ++ tailWord_3367040).sum := by decide
  have hdescent : baseEnd_3367040 < baseStart_3367040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367063 : List Nat := [1, 1, 3, 3, 5, 1, 1, 3, 4]
def baseStart_3367063 : Nat := 118140960795 + 3367063 * 2 ^ 59
def prefixEnd_3367063 : Nat := 4983230072969 + 3 ^ 40 * 3367063 * 2
def baseEnd_3367063 : Nat := 384204825104370018717259

theorem tailTrace_3367063 : CollatzResearch.WordTrace tailWord_3367063 prefixEnd_3367063 384204825104370018717259 := by
  unfold tailWord_3367063
  simp only [CollatzResearch.WordTrace]
  refine ⟨122806876600713274423553843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81871251067142182949035895 122806876600713274423553843)
  ·
    refine ⟨184210314901069911635330765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122806876600713274423553843 184210314901069911635330765)
    ·
      refine ⟨69078868087901216863249037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184210314901069911635330765 69078868087901216863249037)
      ·
        refine ⟨25904575532962956323718389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69078868087901216863249037 25904575532962956323718389)
        ·
          refine ⟨2428553956215277155348599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25904575532962956323718389 2428553956215277155348599)
          ·
            refine ⟨3642830934322915733022899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2428553956215277155348599 3642830934322915733022899)
            ·
              refine ⟨5464246401484373599534349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3642830934322915733022899 5464246401484373599534349)
              ·
                refine ⟨2049092400556640099825381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5464246401484373599534349 2049092400556640099825381)
                ·
                  refine ⟨384204825104370018717259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2049092400556640099825381 384204825104370018717259)
                  ·
                    rfl

theorem cell22_3367063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 3, 4].length) (baseStart_3367063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3367063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3367063 prefixEnd_3367063 := by exact prefixLift 3367063
  have htrace : WordTrace (prefixWord ++ tailWord_3367063) baseStart_3367063 baseEnd_3367063 := by
    simpa [prefixWord, tailWord_3367063, baseEnd_3367063] using wordTrace_append hprefix tailTrace_3367063
  have hstable : (prefixWord ++ tailWord_3367063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367063).length < 2 ^ (prefixWord ++ tailWord_3367063).sum := by decide
  have hdescent : baseEnd_3367063 < baseStart_3367063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367074 : List Nat := [3, 3, 1, 3, 1, 3, 8]
def baseStart_3367074 : Nat := 118140960795 + 3367074 * 2 ^ 59
def prefixEnd_3367074 : Nat := 4983230072969 + 3 ^ 40 * 3367074 * 2
def baseEnd_3367074 : Nat := 42689564475478136819509

theorem tailTrace_3367074 : CollatzResearch.WordTrace tailWord_3367074 prefixEnd_3367074 42689564475478136819509 := by
  unfold tailWord_3367074
  simp only [CollatzResearch.WordTrace]
  refine ⟨30701819450918355825551069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81871518535782282201469517 30701819450918355825551069)
  ·
    refine ⟨11513182294094383434581651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30701819450918355825551069 11513182294094383434581651)
    ·
      refine ⟨17269773441141575151872477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11513182294094383434581651 17269773441141575151872477)
      ·
        refine ⟨6476165040428090681952179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17269773441141575151872477 6476165040428090681952179)
        ·
          refine ⟨9714247560642136022928269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6476165040428090681952179 9714247560642136022928269)
          ·
            refine ⟨3642842835240801008598101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9714247560642136022928269 3642842835240801008598101)
            ·
              refine ⟨42689564475478136819509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3642842835240801008598101 42689564475478136819509)
              ·
                rfl

theorem cell22_3367074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 8].length) (baseStart_3367074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3367074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3367074 prefixEnd_3367074 := by exact prefixLift 3367074
  have htrace : WordTrace (prefixWord ++ tailWord_3367074) baseStart_3367074 baseEnd_3367074 := by
    simpa [prefixWord, tailWord_3367074, baseEnd_3367074] using wordTrace_append hprefix tailTrace_3367074
  have hstable : (prefixWord ++ tailWord_3367074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367074).length < 2 ^ (prefixWord ++ tailWord_3367074).sum := by decide
  have hdescent : baseEnd_3367074 < baseStart_3367074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367147 : List Nat := [1, 1, 1, 1, 2, 5, 2, 3, 6]
def baseStart_3367147 : Nat := 118140960795 + 3367147 * 2 ^ 59
def prefixEnd_3367147 : Nat := 4983230072969 + 3 ^ 40 * 3367147 * 2
def baseEnd_3367147 : Nat := 384214410076587279017173

theorem tailTrace_3367147 : CollatzResearch.WordTrace tailWord_3367147 prefixEnd_3367147 384214410076587279017173 := by
  unfold tailWord_3367147
  simp only [CollatzResearch.WordTrace]
  refine ⟨122809940332408956769611695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81873293554939304513074463 122809940332408956769611695)
  ·
    refine ⟨184214910498613435154417543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122809940332408956769611695 184214910498613435154417543)
    ·
      refine ⟨276322365747920152731626315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184214910498613435154417543 276322365747920152731626315)
      ·
        refine ⟨414483548621880229097439473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276322365747920152731626315 414483548621880229097439473)
        ·
          refine ⟨310862661466410171823079605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 414483548621880229097439473 310862661466410171823079605)
          ·
            refine ⟨29143374512475953608413713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 310862661466410171823079605 29143374512475953608413713)
            ·
              refine ⟨21857530884356965206310285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29143374512475953608413713 21857530884356965206310285)
              ·
                refine ⟨8196574081633861952366357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21857530884356965206310285 8196574081633861952366357)
                ·
                  refine ⟨384214410076587279017173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8196574081633861952366357 384214410076587279017173)
                  ·
                    rfl

theorem cell22_3367147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3, 6].length) (baseStart_3367147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3367147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3367147 prefixEnd_3367147 := by exact prefixLift 3367147
  have htrace : WordTrace (prefixWord ++ tailWord_3367147) baseStart_3367147 baseEnd_3367147 := by
    simpa [prefixWord, tailWord_3367147, baseEnd_3367147] using wordTrace_append hprefix tailTrace_3367147
  have hstable : (prefixWord ++ tailWord_3367147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367147).length < 2 ^ (prefixWord ++ tailWord_3367147).sum := by decide
  have hdescent : baseEnd_3367147 < baseStart_3367147 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367164 : List Nat := [2, 2, 2, 1, 4, 2, 1, 2, 6]
def baseStart_3367164 : Nat := 118140960795 + 3367164 * 2 ^ 59
def prefixEnd_3367164 : Nat := 4983230072969 + 3 ^ 40 * 3367164 * 2
def baseEnd_3367164 : Nat := 384216349892393153125489

theorem tailTrace_3367164 : CollatzResearch.WordTrace tailWord_3367164 prefixEnd_3367164 384216349892393153125489 := by
  unfold tailWord_3367164
  simp only [CollatzResearch.WordTrace]
  refine ⟨61405280186673684336490273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81873706915564912448653697 61405280186673684336490273)
  ·
    refine ⟨46053960140005263252367705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61405280186673684336490273 46053960140005263252367705)
    ·
      refine ⟨34540470105003947439275779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46053960140005263252367705 34540470105003947439275779)
      ·
        refine ⟨51810705157505921158913669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34540470105003947439275779 51810705157505921158913669)
        ·
          refine ⟨9714507217032360217296313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51810705157505921158913669 9714507217032360217296313)
          ·
            refine ⟨7285880412774270162972235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9714507217032360217296313 7285880412774270162972235)
            ·
              refine ⟨10928820619161405244458353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7285880412774270162972235 10928820619161405244458353)
              ·
                refine ⟨8196615464371053933343765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10928820619161405244458353 8196615464371053933343765)
                ·
                  refine ⟨384216349892393153125489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8196615464371053933343765 384216349892393153125489)
                  ·
                    rfl

theorem cell22_3367164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 2, 6].length) (baseStart_3367164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3367164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3367164 prefixEnd_3367164 := by exact prefixLift 3367164
  have htrace : WordTrace (prefixWord ++ tailWord_3367164) baseStart_3367164 baseEnd_3367164 := by
    simpa [prefixWord, tailWord_3367164, baseEnd_3367164] using wordTrace_append hprefix tailTrace_3367164
  have hstable : (prefixWord ++ tailWord_3367164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367164).length < 2 ^ (prefixWord ++ tailWord_3367164).sum := by decide
  have hdescent : baseEnd_3367164 < baseStart_3367164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367166 : List Nat := [4, 2, 2, 1, 1, 1, 2, 4, 1, 4]
def baseStart_3367166 : Nat := 118140960795 + 3367166 * 2 ^ 59
def prefixEnd_3367166 : Nat := 4983230072969 + 3 ^ 40 * 3367166 * 2
def baseEnd_3367166 : Nat := 1152649734318052120826461

theorem tailTrace_3367166 : CollatzResearch.WordTrace tailWord_3367166 prefixEnd_3367166 1152649734318052120826461 := by
  unfold tailWord_3367166
  simp only [CollatzResearch.WordTrace]
  refine ⟨15351329164917515376819169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81873755546226748676368901 15351329164917515376819169)
  ·
    refine ⟨11513496873688136532614377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15351329164917515376819169 11513496873688136532614377)
    ·
      refine ⟨8635122655266102399460783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11513496873688136532614377 8635122655266102399460783)
      ·
        refine ⟨12952683982899153599191175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8635122655266102399460783 12952683982899153599191175)
        ·
          refine ⟨19429025974348730398786763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12952683982899153599191175 19429025974348730398786763)
          ·
            refine ⟨29143538961523095598180145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19429025974348730398786763 29143538961523095598180145)
            ·
              refine ⟨21857654221142321698635109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29143538961523095598180145 21857654221142321698635109)
              ·
                refine ⟨4098310166464185318494083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21857654221142321698635109 4098310166464185318494083)
                ·
                  refine ⟨6147465249696277977741125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4098310166464185318494083 6147465249696277977741125)
                  ·
                    refine ⟨1152649734318052120826461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6147465249696277977741125 1152649734318052120826461)
                    ·
                      rfl

theorem cell22_3367166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_3367166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3367166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3367166 prefixEnd_3367166 := by exact prefixLift 3367166
  have htrace : WordTrace (prefixWord ++ tailWord_3367166) baseStart_3367166 baseEnd_3367166 := by
    simpa [prefixWord, tailWord_3367166, baseEnd_3367166] using wordTrace_append hprefix tailTrace_3367166
  have hstable : (prefixWord ++ tailWord_3367166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367166).length < 2 ^ (prefixWord ++ tailWord_3367166).sum := by decide
  have hdescent : baseEnd_3367166 < baseStart_3367166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367179 : List Nat := [1, 1, 1, 1, 5, 2, 2, 2, 4, 3]
def baseStart_3367179 : Nat := 118140960795 + 3367179 * 2 ^ 59
def prefixEnd_3367179 : Nat := 4983230072969 + 3 ^ 40 * 3367179 * 2
def baseEnd_3367179 : Nat := 1152654184483724420251421

theorem tailTrace_3367179 : CollatzResearch.WordTrace tailWord_3367179 prefixEnd_3367179 1152654184483724420251421 := by
  unfold tailWord_3367179
  simp only [CollatzResearch.WordTrace]
  refine ⟨122811107468293026234776591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81874071645528684156517727 122811107468293026234776591)
  ·
    refine ⟨184216661202439539352164887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122811107468293026234776591 184216661202439539352164887)
    ·
      refine ⟨276324991803659309028247331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184216661202439539352164887 276324991803659309028247331)
      ·
        refine ⟨414487487705488963542370997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276324991803659309028247331 414487487705488963542370997)
        ·
          refine ⟨38858201972389590332097281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 414487487705488963542370997 38858201972389590332097281)
          ·
            refine ⟨29143651479292192749072961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38858201972389590332097281 29143651479292192749072961)
            ·
              refine ⟨21857738609469144561804721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29143651479292192749072961 21857738609469144561804721)
              ·
                refine ⟨16393303957101858421353541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21857738609469144561804721 16393303957101858421353541)
                ·
                  refine ⟨3073744491956598454003789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16393303957101858421353541 3073744491956598454003789)
                  ·
                    refine ⟨1152654184483724420251421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3073744491956598454003789 1152654184483724420251421)
                    ·
                      rfl

theorem cell22_3367179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 4, 3].length) (baseStart_3367179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3367179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3367179 prefixEnd_3367179 := by exact prefixLift 3367179
  have htrace : WordTrace (prefixWord ++ tailWord_3367179) baseStart_3367179 baseEnd_3367179 := by
    simpa [prefixWord, tailWord_3367179, baseEnd_3367179] using wordTrace_append hprefix tailTrace_3367179
  have hstable : (prefixWord ++ tailWord_3367179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367179).length < 2 ^ (prefixWord ++ tailWord_3367179).sum := by decide
  have hdescent : baseEnd_3367179 < baseStart_3367179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367192 : List Nat := [2, 1, 2, 3, 1, 2, 11]
def baseStart_3367192 : Nat := 118140960795 + 3367192 * 2 ^ 59
def prefixEnd_3367192 : Nat := 4983230072969 + 3 ^ 40 * 3367192 * 2
def baseEnd_3367192 : Nat := 42691060542570248876903

theorem tailTrace_3367192 : CollatzResearch.WordTrace tailWord_3367192 prefixEnd_3367192 42691060542570248876903 := by
  unfold tailWord_3367192
  simp only [CollatzResearch.WordTrace]
  refine ⟨61405790808622964727499915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81874387744830619636666553 61405790808622964727499915)
  ·
    refine ⟨92108686212934447091249873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61405790808622964727499915 92108686212934447091249873)
    ·
      refine ⟨69081514659700835318437405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92108686212934447091249873 69081514659700835318437405)
      ·
        refine ⟨25905567997387813244414027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69081514659700835318437405 25905567997387813244414027)
        ·
          refine ⟨38858351996081719866621041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25905567997387813244414027 38858351996081719866621041)
          ·
            refine ⟨29143763997061289899965781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38858351996081719866621041 29143763997061289899965781)
            ·
              refine ⟨42691060542570248876903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 29143763997061289899965781 42691060542570248876903)
              ·
                rfl

theorem cell22_3367192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 11].length) (baseStart_3367192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3367192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3367192 prefixEnd_3367192 := by exact prefixLift 3367192
  have htrace : WordTrace (prefixWord ++ tailWord_3367192) baseStart_3367192 baseEnd_3367192 := by
    simpa [prefixWord, tailWord_3367192, baseEnd_3367192] using wordTrace_append hprefix tailTrace_3367192
  have hstable : (prefixWord ++ tailWord_3367192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367192).length < 2 ^ (prefixWord ++ tailWord_3367192).sum := by decide
  have hdescent : baseEnd_3367192 < baseStart_3367192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367198 : List Nat := [4, 3, 2, 1, 1, 2, 2, 1, 6]
def baseStart_3367198 : Nat := 118140960795 + 3367198 * 2 ^ 59
def prefixEnd_3367198 : Nat := 4983230072969 + 3 ^ 40 * 3367198 * 2
def baseEnd_3367198 : Nat := 384220229524004901342121

theorem tailTrace_3367198 : CollatzResearch.WordTrace tailWord_3367198 prefixEnd_3367198 384220229524004901342121 := by
  unfold tailWord_3367198
  simp only [CollatzResearch.WordTrace]
  refine ⟨15351475056903024059964781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81874533636816128319812165 15351475056903024059964781)
  ·
    refine ⟨5756803146338634022486793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15351475056903024059964781 5756803146338634022486793)
    ·
      refine ⟨4317602359753975516865095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5756803146338634022486793 4317602359753975516865095)
      ·
        refine ⟨6476403539630963275297643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4317602359753975516865095 6476403539630963275297643)
        ·
          refine ⟨9714605309446444912946465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6476403539630963275297643 9714605309446444912946465)
          ·
            refine ⟨7285953982084833684709849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9714605309446444912946465 7285953982084833684709849)
            ·
              refine ⟨5464465486563625263532387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7285953982084833684709849 5464465486563625263532387)
              ·
                refine ⟨8196698229845437895298581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5464465486563625263532387 8196698229845437895298581)
                ·
                  refine ⟨384220229524004901342121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8196698229845437895298581 384220229524004901342121)
                  ·
                    rfl

theorem cell22_3367198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_3367198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3367198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3367198 prefixEnd_3367198 := by exact prefixLift 3367198
  have htrace : WordTrace (prefixWord ++ tailWord_3367198) baseStart_3367198 baseEnd_3367198 := by
    simpa [prefixWord, tailWord_3367198, baseEnd_3367198] using wordTrace_append hprefix tailTrace_3367198
  have hstable : (prefixWord ++ tailWord_3367198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367198).length < 2 ^ (prefixWord ++ tailWord_3367198).sum := by decide
  have hdescent : baseEnd_3367198 < baseStart_3367198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367226 : List Nat := [3, 1, 1, 1, 4, 4, 2, 6]
def baseStart_3367226 : Nat := 118140960795 + 3367226 * 2 ^ 59
def prefixEnd_3367226 : Nat := 4983230072969 + 3 ^ 40 * 3367226 * 2
def baseEnd_3367226 : Nat := 128074474838247996036253

theorem tailTrace_3367226 : CollatzResearch.WordTrace tailWord_3367226 prefixEnd_3367226 128074474838247996036253 := by
  unfold tailWord_3367226
  simp only [CollatzResearch.WordTrace]
  refine ⟨30703205424780688315434383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81875214466081835507825021 30703205424780688315434383)
  ·
    refine ⟨46054808137171032473151575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30703205424780688315434383 46054808137171032473151575)
    ·
      refine ⟨69082212205756548709727363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46054808137171032473151575 69082212205756548709727363)
      ·
        refine ⟨103623318308634823064591045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69082212205756548709727363 103623318308634823064591045)
        ·
          refine ⟨19429372182869029324610821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103623318308634823064591045 19429372182869029324610821)
          ·
            refine ⟨3643007284287942998364529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19429372182869029324610821 3643007284287942998364529)
            ·
              refine ⟨2732255463215957248773397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3643007284287942998364529 2732255463215957248773397)
              ·
                refine ⟨128074474838247996036253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2732255463215957248773397 128074474838247996036253)
                ·
                  rfl

theorem cell22_3367226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2, 6].length) (baseStart_3367226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3367226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3367226 prefixEnd_3367226 := by exact prefixLift 3367226
  have htrace : WordTrace (prefixWord ++ tailWord_3367226) baseStart_3367226 baseEnd_3367226 := by
    simpa [prefixWord, tailWord_3367226, baseEnd_3367226] using wordTrace_append hprefix tailTrace_3367226
  have hstable : (prefixWord ++ tailWord_3367226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367226).length < 2 ^ (prefixWord ++ tailWord_3367226).sum := by decide
  have hdescent : baseEnd_3367226 < baseStart_3367226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367271 : List Nat := [1, 1, 5, 1, 3, 2, 1, 3, 5]
def baseStart_3367271 : Nat := 118140960795 + 3367271 * 2 ^ 59
def prefixEnd_3367271 : Nat := 4983230072969 + 3 ^ 40 * 3367271 * 2
def baseEnd_3367271 : Nat := 384228559321288948983713

theorem tailTrace_3367271 : CollatzResearch.WordTrace tailWord_3367271 prefixEnd_3367271 384228559321288948983713 := by
  unfold tailWord_3367271
  simp only [CollatzResearch.WordTrace]
  refine ⟨122814462983959725947125667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81876308655973150631417111 122814462983959725947125667)
  ·
    refine ⟨184221694475939588920688501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122814462983959725947125667 184221694475939588920688501)
    ·
      refine ⟨17270783857119336461314547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 184221694475939588920688501 17270783857119336461314547)
      ·
        refine ⟨25906175785679004691971821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17270783857119336461314547 25906175785679004691971821)
        ·
          refine ⟨9714815919629626759489433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25906175785679004691971821 9714815919629626759489433)
          ·
            refine ⟨7286111939722220069617075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9714815919629626759489433 7286111939722220069617075)
            ·
              refine ⟨10929167909583330104425613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7286111939722220069617075 10929167909583330104425613)
              ·
                refine ⟨4098437966093748789159605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10929167909583330104425613 4098437966093748789159605)
                ·
                  refine ⟨384228559321288948983713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4098437966093748789159605 384228559321288948983713)
                  ·
                    rfl

theorem cell22_3367271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 3, 5].length) (baseStart_3367271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3367271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3367271 prefixEnd_3367271 := by exact prefixLift 3367271
  have htrace : WordTrace (prefixWord ++ tailWord_3367271) baseStart_3367271 baseEnd_3367271 := by
    simpa [prefixWord, tailWord_3367271, baseEnd_3367271] using wordTrace_append hprefix tailTrace_3367271
  have hstable : (prefixWord ++ tailWord_3367271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367271).length < 2 ^ (prefixWord ++ tailWord_3367271).sum := by decide
  have hdescent : baseEnd_3367271 < baseStart_3367271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367331 : List Nat := [1, 1, 1, 4, 1, 5, 2, 1, 1, 5]
def baseStart_3367331 : Nat := 118140960795 + 3367331 * 2 ^ 59
def prefixEnd_3367331 : Nat := 4983230072969 + 3 ^ 40 * 3367331 * 2
def baseEnd_3367331 : Nat := 1152706217190046690450955

theorem tailTrace_3367331 : CollatzResearch.WordTrace tailWord_3367331 prefixEnd_3367331 1152706217190046690450955 := by
  unfold tailWord_3367331
  simp only [CollatzResearch.WordTrace]
  refine ⟨122816651363742356194309847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81877767575828237462873231 122816651363742356194309847)
  ·
    refine ⟨184224977045613534291464771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122816651363742356194309847 184224977045613534291464771)
    ·
      refine ⟨276337465568420301437197157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184224977045613534291464771 276337465568420301437197157)
      ·
        refine ⟨51813274794078806519474467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 276337465568420301437197157 51813274794078806519474467)
        ·
          refine ⟨77719912191118209779211701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51813274794078806519474467 77719912191118209779211701)
          ·
            refine ⟨7286241767917332166801097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77719912191118209779211701 7286241767917332166801097)
            ·
              refine ⟨5464681325937999125100823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7286241767917332166801097 5464681325937999125100823)
              ·
                refine ⟨8197021988906998687651235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5464681325937999125100823 8197021988906998687651235)
                ·
                  refine ⟨12295532983360498031476853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8197021988906998687651235 12295532983360498031476853)
                  ·
                    refine ⟨1152706217190046690450955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12295532983360498031476853 1152706217190046690450955)
                    ·
                      rfl

theorem cell22_3367331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 1, 1, 5].length) (baseStart_3367331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3367331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3367331 prefixEnd_3367331 := by exact prefixLift 3367331
  have htrace : WordTrace (prefixWord ++ tailWord_3367331) baseStart_3367331 baseEnd_3367331 := by
    simpa [prefixWord, tailWord_3367331, baseEnd_3367331] using wordTrace_append hprefix tailTrace_3367331
  have hstable : (prefixWord ++ tailWord_3367331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367331).length < 2 ^ (prefixWord ++ tailWord_3367331).sum := by decide
  have hdescent : baseEnd_3367331 < baseStart_3367331 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367382 : List Nat := [5, 2, 1, 1, 1, 1, 5, 1, 2, 3]
def baseStart_3367382 : Nat := 118140960795 + 3367382 * 2 ^ 59
def prefixEnd_3367382 : Nat := 4983230072969 + 3 ^ 40 * 3367382 * 2
def baseEnd_3367382 : Nat := 1152723675532299557425799

theorem tailTrace_3367382 : CollatzResearch.WordTrace tailWord_3367382 prefixEnd_3367382 1152723675532299557425799 := by
  unfold tailWord_3367382
  simp only [CollatzResearch.WordTrace]
  refine ⟨7676156967909849494026025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81879007657705061269610933 7676156967909849494026025)
  ·
    refine ⟨5757117725932387120519519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7676156967909849494026025 5757117725932387120519519)
    ·
      refine ⟨8635676588898580680779279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5757117725932387120519519 8635676588898580680779279)
      ·
        refine ⟨12953514883347871021168919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8635676588898580680779279 12953514883347871021168919)
        ·
          refine ⟨19430272325021806531753379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12953514883347871021168919 19430272325021806531753379)
          ·
            refine ⟨29145408487532709797630069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19430272325021806531753379 29145408487532709797630069)
            ·
              refine ⟨2732382045706191543527819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29145408487532709797630069 2732382045706191543527819)
              ·
                refine ⟨4098573068559287315291729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2732382045706191543527819 4098573068559287315291729)
                ·
                  refine ⟨3073929801419465486468797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4098573068559287315291729 3073929801419465486468797)
                  ·
                    refine ⟨1152723675532299557425799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3073929801419465486468797 1152723675532299557425799)
                    ·
                      rfl

theorem cell22_3367382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_3367382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3367382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3367382 prefixEnd_3367382 := by exact prefixLift 3367382
  have htrace : WordTrace (prefixWord ++ tailWord_3367382) baseStart_3367382 baseEnd_3367382 := by
    simpa [prefixWord, tailWord_3367382, baseEnd_3367382] using wordTrace_append hprefix tailTrace_3367382
  have hstable : (prefixWord ++ tailWord_3367382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367382).length < 2 ^ (prefixWord ++ tailWord_3367382).sum := by decide
  have hdescent : baseEnd_3367382 < baseStart_3367382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367395 : List Nat := [1, 1, 1, 6, 4, 1, 2, 6]
def baseStart_3367395 : Nat := 118140960795 + 3367395 * 2 ^ 59
def prefixEnd_3367395 : Nat := 4983230072969 + 3 ^ 40 * 3367395 * 2
def baseEnd_3367395 : Nat := 128080902855330206316751

theorem tailTrace_3367395 : CollatzResearch.WordTrace tailWord_3367395 prefixEnd_3367395 128080902855330206316751 := by
  unfold tailWord_3367395
  simp only [CollatzResearch.WordTrace]
  refine ⟨122818985635510495124639639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81879323757006996749759759 122818985635510495124639639)
  ·
    refine ⟨184228478453265742686959459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122818985635510495124639639 184228478453265742686959459)
    ·
      refine ⟨276342717679898614030439189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184228478453265742686959459 276342717679898614030439189)
      ·
        refine ⟨12953564891245247532676837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 276342717679898614030439189 12953564891245247532676837)
        ·
          refine ⟨2428793417108483912376907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12953564891245247532676837 2428793417108483912376907)
          ·
            refine ⟨3643190125662725868565361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2428793417108483912376907 3643190125662725868565361)
            ·
              refine ⟨2732392594247044401424021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3643190125662725868565361 2732392594247044401424021)
              ·
                refine ⟨128080902855330206316751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2732392594247044401424021 128080902855330206316751)
                ·
                  rfl

theorem cell22_3367395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 2, 6].length) (baseStart_3367395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3367395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3367395 prefixEnd_3367395 := by exact prefixLift 3367395
  have htrace : WordTrace (prefixWord ++ tailWord_3367395) baseStart_3367395 baseEnd_3367395 := by
    simpa [prefixWord, tailWord_3367395, baseEnd_3367395] using wordTrace_append hprefix tailTrace_3367395
  have hstable : (prefixWord ++ tailWord_3367395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367395).length < 2 ^ (prefixWord ++ tailWord_3367395).sum := by decide
  have hdescent : baseEnd_3367395 < baseStart_3367395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367406 : List Nat := [4, 1, 2, 1, 2, 2, 1, 2, 7]
def baseStart_3367406 : Nat := 118140960795 + 3367406 * 2 ^ 59
def prefixEnd_3367406 : Nat := 4983230072969 + 3 ^ 40 * 3367406 * 2
def baseEnd_3367406 : Nat := 384243963740923831608575

theorem tailTrace_3367406 : CollatzResearch.WordTrace tailWord_3367406 prefixEnd_3367406 384243963740923831608575 := by
  unfold tailWord_3367406
  simp only [CollatzResearch.WordTrace]
  refine ⟨15352423354808830500411259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81879591225647096002193381 15352423354808830500411259)
  ·
    refine ⟨23028635032213245750616889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15352423354808830500411259 23028635032213245750616889)
    ·
      refine ⟨17271476274159934312962667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23028635032213245750616889 17271476274159934312962667)
      ·
        refine ⟨25907214411239901469444001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17271476274159934312962667 25907214411239901469444001)
        ·
          refine ⟨19430410808429926102083001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25907214411239901469444001 19430410808429926102083001)
          ·
            refine ⟨14572808106322444576562251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19430410808429926102083001 14572808106322444576562251)
            ·
              refine ⟨21859212159483666864843377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14572808106322444576562251 21859212159483666864843377)
              ·
                refine ⟨16394409119612750148632533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21859212159483666864843377 16394409119612750148632533)
                ·
                  refine ⟨384243963740923831608575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16394409119612750148632533 384243963740923831608575)
                  ·
                    rfl

theorem cell22_3367406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 7].length) (baseStart_3367406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3367406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3367406 prefixEnd_3367406 := by exact prefixLift 3367406
  have htrace : WordTrace (prefixWord ++ tailWord_3367406) baseStart_3367406 baseEnd_3367406 := by
    simpa [prefixWord, tailWord_3367406, baseEnd_3367406] using wordTrace_append hprefix tailTrace_3367406
  have hstable : (prefixWord ++ tailWord_3367406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367406).length < 2 ^ (prefixWord ++ tailWord_3367406).sum := by decide
  have hdescent : baseEnd_3367406 < baseStart_3367406 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367453 : List Nat := [1, 4, 2, 2, 1, 3, 1, 1, 3, 4]
def baseStart_3367453 : Nat := 118140960795 + 3367453 * 2 ^ 59
def prefixEnd_3367453 : Nat := 4983230072969 + 3 ^ 40 * 3367453 * 2
def baseEnd_3367453 : Nat := 1152747980283279038900581

theorem tailTrace_3367453 : CollatzResearch.WordTrace tailWord_3367453 prefixEnd_3367453 1152747980283279038900581 := by
  unfold tailWord_3367453
  simp only [CollatzResearch.WordTrace]
  refine ⟨122821101069300371030251013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81880734046200247353500675 122821101069300371030251013)
  ·
    refine ⟨23028956450493819568172065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122821101069300371030251013 23028956450493819568172065)
    ·
      refine ⟨17271717337870364676129049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23028956450493819568172065 17271717337870364676129049)
      ·
        refine ⟨12953788003402773507096787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17271717337870364676129049 12953788003402773507096787)
        ·
          refine ⟨19430682005104160260645181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12953788003402773507096787 19430682005104160260645181)
          ·
            refine ⟨7286505751914060097741943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19430682005104160260645181 7286505751914060097741943)
            ·
              refine ⟨10929758627871090146612915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7286505751914060097741943 10929758627871090146612915)
              ·
                refine ⟨16394637941806635219919373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10929758627871090146612915 16394637941806635219919373)
                ·
                  refine ⟨6147989228177488207469765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16394637941806635219919373 6147989228177488207469765)
                  ·
                    refine ⟨1152747980283279038900581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6147989228177488207469765 1152747980283279038900581)
                    ·
                      rfl

theorem cell22_3367453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_3367453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3367453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3367453 prefixEnd_3367453 := by exact prefixLift 3367453
  have htrace : WordTrace (prefixWord ++ tailWord_3367453) baseStart_3367453 baseEnd_3367453 := by
    simpa [prefixWord, tailWord_3367453, baseEnd_3367453] using wordTrace_append hprefix tailTrace_3367453
  have hstable : (prefixWord ++ tailWord_3367453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367453).length < 2 ^ (prefixWord ++ tailWord_3367453).sum := by decide
  have hdescent : baseEnd_3367453 < baseStart_3367453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367485 : List Nat := [1, 4, 1, 3, 2, 2, 1, 4, 4]
def baseStart_3367485 : Nat := 118140960795 + 3367485 * 2 ^ 59
def prefixEnd_3367485 : Nat := 4983230072969 + 3 ^ 40 * 3367485 * 2
def baseEnd_3367485 : Nat := 384252978179080540700161

theorem tailTrace_3367485 : CollatzResearch.WordTrace tailWord_3367485 prefixEnd_3367485 384252978179080540700161 := by
  unfold tailWord_3367485
  simp only [CollatzResearch.WordTrace]
  refine ⟨122822268205184440495415909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81881512136789626996943939 122822268205184440495415909)
  ·
    refine ⟨23029175288472082592890483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122822268205184440495415909 23029175288472082592890483)
    ·
      refine ⟨34543762932708123889335725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23029175288472082592890483 34543762932708123889335725)
      ·
        refine ⟨12953911099765546458500897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34543762932708123889335725 12953911099765546458500897)
        ·
          refine ⟨9715433324824159843875673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12953911099765546458500897 9715433324824159843875673)
          ·
            refine ⟨7286574993618119882906755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9715433324824159843875673 7286574993618119882906755)
            ·
              refine ⟨10929862490427179824360133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7286574993618119882906755 10929862490427179824360133)
              ·
                refine ⟨2049349216955096217067525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10929862490427179824360133 2049349216955096217067525)
                ·
                  refine ⟨384252978179080540700161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2049349216955096217067525 384252978179080540700161)
                  ·
                    rfl

theorem cell22_3367485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 4, 4].length) (baseStart_3367485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3367485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3367485 prefixEnd_3367485 := by exact prefixLift 3367485
  have htrace : WordTrace (prefixWord ++ tailWord_3367485) baseStart_3367485 baseEnd_3367485 := by
    simpa [prefixWord, tailWord_3367485, baseEnd_3367485] using wordTrace_append hprefix tailTrace_3367485
  have hstable : (prefixWord ++ tailWord_3367485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367485).length < 2 ^ (prefixWord ++ tailWord_3367485).sum := by decide
  have hdescent : baseEnd_3367485 < baseStart_3367485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367545 : List Nat := [1, 2, 1, 3, 3, 3, 2, 1, 3, 3]
def baseStart_3367545 : Nat := 118140960795 + 3367545 * 2 ^ 59
def prefixEnd_3367545 : Nat := 4983230072969 + 3 ^ 40 * 3367545 * 2
def baseEnd_3367545 : Nat := 1152779473763421465600299

theorem tailTrace_3367545 : CollatzResearch.WordTrace tailWord_3367545 prefixEnd_3367545 1152779473763421465600299 := by
  unfold tailWord_3367545
  simp only [CollatzResearch.WordTrace]
  refine ⟨122824456584967070742600089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81882971056644713828400059 122824456584967070742600089)
  ·
    refine ⟨92118342438725303056950067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122824456584967070742600089 92118342438725303056950067)
    ·
      refine ⟨138177513658087954585425101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92118342438725303056950067 138177513658087954585425101)
      ·
        refine ⟨51816567621782982969534413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138177513658087954585425101 51816567621782982969534413)
        ·
          refine ⟨19431212858168618613575405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51816567621782982969534413 19431212858168618613575405)
          ·
            refine ⟨7286704821813231980090777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19431212858168618613575405 7286704821813231980090777)
            ·
              refine ⟨5465028616359923985068083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7286704821813231980090777 5465028616359923985068083)
              ·
                refine ⟨8197542924539885977602125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5465028616359923985068083 8197542924539885977602125)
                ·
                  refine ⟨3074078596702457241600797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8197542924539885977602125 3074078596702457241600797)
                  ·
                    refine ⟨1152779473763421465600299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3074078596702457241600797 1152779473763421465600299)
                    ·
                      rfl

theorem cell22_3367545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 1, 3, 3].length) (baseStart_3367545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3367545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3367545 prefixEnd_3367545 := by exact prefixLift 3367545
  have htrace : WordTrace (prefixWord ++ tailWord_3367545) baseStart_3367545 baseEnd_3367545 := by
    simpa [prefixWord, tailWord_3367545, baseEnd_3367545] using wordTrace_append hprefix tailTrace_3367545
  have hstable : (prefixWord ++ tailWord_3367545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367545).length < 2 ^ (prefixWord ++ tailWord_3367545).sum := by decide
  have hdescent : baseEnd_3367545 < baseStart_3367545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367603 : List Nat := [1, 1, 1, 2, 3, 4, 3, 1, 6]
def baseStart_3367603 : Nat := 118140960795 + 3367603 * 2 ^ 59
def prefixEnd_3367603 : Nat := 4983230072969 + 3 ^ 40 * 3367603 * 2
def baseEnd_3367603 : Nat := 384266442782909549216707

theorem tailTrace_3367603 : CollatzResearch.WordTrace tailWord_3367603 prefixEnd_3367603 384266442782909549216707 := by
  unfold tailWord_3367603
  simp only [CollatzResearch.WordTrace]
  refine ⟨122826572018756946648211463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81884381345837964432140975 122826572018756946648211463)
  ·
    refine ⟨184239858028135419972317195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122826572018756946648211463 184239858028135419972317195)
    ·
      refine ⟨276359787042203129958475793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184239858028135419972317195 276359787042203129958475793)
      ·
        refine ⟨207269840281652347468856845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276359787042203129958475793 207269840281652347468856845)
        ·
          refine ⟨77726190105619630300821317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207269840281652347468856845 77726190105619630300821317)
          ·
            refine ⟨14573660644803680681403997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77726190105619630300821317 14573660644803680681403997)
            ·
              refine ⟨5465122741801380255526499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14573660644803680681403997 5465122741801380255526499)
              ·
                refine ⟨8197684112702070383289749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5465122741801380255526499 8197684112702070383289749)
                ·
                  refine ⟨384266442782909549216707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8197684112702070383289749 384266442782909549216707)
                  ·
                    rfl

theorem cell22_3367603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 1, 6].length) (baseStart_3367603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3367603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3367603 prefixEnd_3367603 := by exact prefixLift 3367603
  have htrace : WordTrace (prefixWord ++ tailWord_3367603) baseStart_3367603 baseEnd_3367603 := by
    simpa [prefixWord, tailWord_3367603, baseEnd_3367603] using wordTrace_append hprefix tailTrace_3367603
  have hstable : (prefixWord ++ tailWord_3367603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367603).length < 2 ^ (prefixWord ++ tailWord_3367603).sum := by decide
  have hdescent : baseEnd_3367603 < baseStart_3367603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367652 : List Nat := [2, 3, 1, 1, 1, 5, 2, 2, 2, 3]
def baseStart_3367652 : Nat := 118140960795 + 3367652 * 2 ^ 59
def prefixEnd_3367652 : Nat := 4983230072969 + 3 ^ 40 * 3367652 * 2
def baseEnd_3367652 : Nat := 1152816102050108853174971

theorem tailTrace_3367652 : CollatzResearch.WordTrace tailWord_3367652 prefixEnd_3367652 1152816102050108853174971 := by
  unfold tailWord_3367652
  simp only [CollatzResearch.WordTrace]
  refine ⟨61414179597789714008372605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81885572797052952011163473 61414179597789714008372605)
  ·
    refine ⟨23030317349171142753139727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61414179597789714008372605 23030317349171142753139727)
    ·
      refine ⟨34545476023756714129709591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23030317349171142753139727 34545476023756714129709591)
      ·
        refine ⟨51818214035635071194564387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34545476023756714129709591 51818214035635071194564387)
        ·
          refine ⟨77727321053452606791846581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51818214035635071194564387 77727321053452606791846581)
          ·
            refine ⟨7286936348761181886735617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77727321053452606791846581 7286936348761181886735617)
            ·
              refine ⟨5465202261570886415051713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7286936348761181886735617 5465202261570886415051713)
              ·
                refine ⟨4098901696178164811288785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5465202261570886415051713 4098901696178164811288785)
                ·
                  refine ⟨3074176272133623608466589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4098901696178164811288785 3074176272133623608466589)
                  ·
                    refine ⟨1152816102050108853174971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3074176272133623608466589 1152816102050108853174971)
                    ·
                      rfl

theorem cell22_3367652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 2, 2, 3].length) (baseStart_3367652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3367652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3367652 prefixEnd_3367652 := by exact prefixLift 3367652
  have htrace : WordTrace (prefixWord ++ tailWord_3367652) baseStart_3367652 baseEnd_3367652 := by
    simpa [prefixWord, tailWord_3367652, baseEnd_3367652] using wordTrace_append hprefix tailTrace_3367652
  have hstable : (prefixWord ++ tailWord_3367652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367652).length < 2 ^ (prefixWord ++ tailWord_3367652).sum := by decide
  have hdescent : baseEnd_3367652 < baseStart_3367652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367682 : List Nat := [3, 4, 1, 1, 1, 3, 3, 6]
def baseStart_3367682 : Nat := 118140960795 + 3367682 * 2 ^ 59
def prefixEnd_3367682 : Nat := 4983230072969 + 3 ^ 40 * 3367682 * 2
def baseEnd_3367682 : Nat := 128091819073688752769431

theorem tailTrace_3367682 : CollatzResearch.WordTrace tailWord_3367682 prefixEnd_3367682 128091819073688752769431 := by
  unfold tailWord_3367682
  simp only [CollatzResearch.WordTrace]
  refine ⟨30707363346367685785084325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81886302256980495426891533 30707363346367685785084325)
  ·
    refine ⟨5757630627443941084703311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30707363346367685785084325 5757630627443941084703311)
    ·
      refine ⟨8636445941165911627054967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5757630627443941084703311 8636445941165911627054967)
      ·
        refine ⟨12954668911748867440582451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8636445941165911627054967 12954668911748867440582451)
        ·
          refine ⟨19432003367623301160873677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12954668911748867440582451 19432003367623301160873677)
          ·
            refine ⟨7287001262858737935327629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19432003367623301160873677 7287001262858737935327629)
            ·
              refine ⟨2732625473572026725747861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7287001262858737935327629 2732625473572026725747861)
              ·
                refine ⟨128091819073688752769431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2732625473572026725747861 128091819073688752769431)
                ·
                  rfl

theorem cell22_3367682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3, 6].length) (baseStart_3367682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3367682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3367682 prefixEnd_3367682 := by exact prefixLift 3367682
  have htrace : WordTrace (prefixWord ++ tailWord_3367682) baseStart_3367682 baseEnd_3367682 := by
    simpa [prefixWord, tailWord_3367682, baseEnd_3367682] using wordTrace_append hprefix tailTrace_3367682
  have hstable : (prefixWord ++ tailWord_3367682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367682).length < 2 ^ (prefixWord ++ tailWord_3367682).sum := by decide
  have hdescent : baseEnd_3367682 < baseStart_3367682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367697 : List Nat := [1, 2, 2, 1, 1, 3, 3, 5, 1, 3]
def baseStart_3367697 : Nat := 118140960795 + 3367697 * 2 ^ 59
def prefixEnd_3367697 : Nat := 4983230072969 + 3 ^ 40 * 3367697 * 2
def baseEnd_3367697 : Nat := 1152831506469743735799833

theorem tailTrace_3367697 : CollatzResearch.WordTrace tailWord_3367697 prefixEnd_3367697 1152831506469743735799833 := by
  unfold tailWord_3367697
  simp only [CollatzResearch.WordTrace]
  refine ⟨122830000480416400702133345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81886666986944267134755563 122830000480416400702133345)
  ·
    refine ⟨92122500360312300526600009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122830000480416400702133345 92122500360312300526600009)
    ·
      refine ⟨69091875270234225394950007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92122500360312300526600009 69091875270234225394950007)
      ·
        refine ⟨103637812905351338092425011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69091875270234225394950007 103637812905351338092425011)
        ·
          refine ⟨155456719358027007138637517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103637812905351338092425011 155456719358027007138637517)
          ·
            refine ⟨58296269759260127676989069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155456719358027007138637517 58296269759260127676989069)
            ·
              refine ⟨21861101159722547878870901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58296269759260127676989069 21861101159722547878870901)
              ·
                refine ⟨2049478233723988863644147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21861101159722547878870901 2049478233723988863644147)
                ·
                  refine ⟨3074217350585983295466221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2049478233723988863644147 3074217350585983295466221)
                  ·
                    refine ⟨1152831506469743735799833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3074217350585983295466221 1152831506469743735799833)
                    ·
                      rfl

theorem cell22_3367697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 5, 1, 3].length) (baseStart_3367697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3367697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3367697 prefixEnd_3367697 := by exact prefixLift 3367697
  have htrace : WordTrace (prefixWord ++ tailWord_3367697) baseStart_3367697 baseEnd_3367697 := by
    simpa [prefixWord, tailWord_3367697, baseEnd_3367697] using wordTrace_append hprefix tailTrace_3367697
  have hstable : (prefixWord ++ tailWord_3367697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367697).length < 2 ^ (prefixWord ++ tailWord_3367697).sum := by decide
  have hdescent : baseEnd_3367697 < baseStart_3367697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367714 : List Nat := [3, 3, 1, 1, 2, 2, 2, 4, 1, 3]
def baseStart_3367714 : Nat := 118140960795 + 3367714 * 2 ^ 59
def prefixEnd_3367714 : Nat := 4983230072969 + 3 ^ 40 * 3367714 * 2
def baseEnd_3367714 : Nat := 1152837325917161358124781

theorem tailTrace_3367714 : CollatzResearch.WordTrace tailWord_3367714 prefixEnd_3367714 1152837325917161358124781 := by
  unfold tailWord_3367714
  simp only [CollatzResearch.WordTrace]
  refine ⟨30707655130338703151375549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81887080347569875070334797 30707655130338703151375549)
  ·
    refine ⟨11515370673877013681765831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30707655130338703151375549 11515370673877013681765831)
    ·
      refine ⟨17273056010815520522648747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11515370673877013681765831 17273056010815520522648747)
      ·
        refine ⟨25909584016223280783973121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17273056010815520522648747 25909584016223280783973121)
        ·
          refine ⟨19432188012167460587979841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25909584016223280783973121 19432188012167460587979841)
          ·
            refine ⟨14574141009125595440984881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19432188012167460587979841 14574141009125595440984881)
            ·
              refine ⟨10930605756844196580738661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14574141009125595440984881 10930605756844196580738661)
              ·
                refine ⟨2049488579408286858888499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10930605756844196580738661 2049488579408286858888499)
                ·
                  refine ⟨3074232869112430288332749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2049488579408286858888499 3074232869112430288332749)
                  ·
                    refine ⟨1152837325917161358124781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3074232869112430288332749 1152837325917161358124781)
                    ·
                      rfl

theorem cell22_3367714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 4, 1, 3].length) (baseStart_3367714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3367714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3367714 prefixEnd_3367714 := by exact prefixLift 3367714
  have htrace : WordTrace (prefixWord ++ tailWord_3367714) baseStart_3367714 baseEnd_3367714 := by
    simpa [prefixWord, tailWord_3367714, baseEnd_3367714] using wordTrace_append hprefix tailTrace_3367714
  have hstable : (prefixWord ++ tailWord_3367714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367714).length < 2 ^ (prefixWord ++ tailWord_3367714).sum := by decide
  have hdescent : baseEnd_3367714 < baseStart_3367714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367772 : List Nat := [2, 2, 4, 2, 1, 1, 3, 1, 6]
def baseStart_3367772 : Nat := 118140960795 + 3367772 * 2 ^ 59
def prefixEnd_3367772 : Nat := 4983230072969 + 3 ^ 40 * 3367772 * 2
def baseEnd_3367772 : Nat := 384285726834156180058201

theorem tailTrace_3367772 : CollatzResearch.WordTrace tailWord_3367772 prefixEnd_3367772 384285726834156180058201 := by
  unfold tailWord_3367772
  simp only [CollatzResearch.WordTrace]
  refine ⟨61416367977572344255556785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81888490636763125674075713 61416367977572344255556785)
  ·
    refine ⟨46062275983179258191667589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61416367977572344255556785 46062275983179258191667589)
    ·
      refine ⟨8636676746846110910937673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46062275983179258191667589 8636676746846110910937673)
      ·
        refine ⟨6477507560134583183203255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8636676746846110910937673 6477507560134583183203255)
        ·
          refine ⟨9716261340201874774804883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6477507560134583183203255 9716261340201874774804883)
          ·
            refine ⟨14574392010302812162207325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9716261340201874774804883 14574392010302812162207325)
            ·
              refine ⟨5465397003863554560827747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14574392010302812162207325 5465397003863554560827747)
              ·
                refine ⟨8198095505795331841241621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5465397003863554560827747 8198095505795331841241621)
                ·
                  refine ⟨384285726834156180058201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8198095505795331841241621 384285726834156180058201)
                  ·
                    rfl

theorem cell22_3367772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 1, 6].length) (baseStart_3367772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3367772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3367772 prefixEnd_3367772 := by exact prefixLift 3367772
  have htrace : WordTrace (prefixWord ++ tailWord_3367772) baseStart_3367772 baseEnd_3367772 := by
    simpa [prefixWord, tailWord_3367772, baseEnd_3367772] using wordTrace_append hprefix tailTrace_3367772
  have hstable : (prefixWord ++ tailWord_3367772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367772).length < 2 ^ (prefixWord ++ tailWord_3367772).sum := by decide
  have hdescent : baseEnd_3367772 < baseStart_3367772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367834 : List Nat := [3, 1, 1, 4, 4, 1, 1, 7]
def baseStart_3367834 : Nat := 118140960795 + 3367834 * 2 ^ 59
def prefixEnd_3367834 : Nat := 4983230072969 + 3 ^ 40 * 3367834 * 2
def baseEnd_3367834 : Nat := 128097600485502338347157

theorem tailTrace_3367834 : CollatzResearch.WordTrace tailWord_3367834 prefixEnd_3367834 128097600485502338347157 := by
  unfold tailWord_3367834
  simp only [CollatzResearch.WordTrace]
  refine ⟨30708749320230018274967639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81889998187280048733247037 30708749320230018274967639)
  ·
    refine ⟨46063123980345027412451459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30708749320230018274967639 46063123980345027412451459)
    ·
      refine ⟨69094685970517541118677189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46063123980345027412451459 69094685970517541118677189)
      ·
        refine ⟨12955253619472038959751973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69094685970517541118677189 12955253619472038959751973)
        ·
          refine ⟨2429110053651007304953495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12955253619472038959751973 2429110053651007304953495)
          ·
            refine ⟨3643665080476510957430243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2429110053651007304953495 3643665080476510957430243)
            ·
              refine ⟨5465497620714766436145365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3643665080476510957430243 5465497620714766436145365)
              ·
                refine ⟨128097600485502338347157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5465497620714766436145365 128097600485502338347157)
                ·
                  rfl

theorem cell22_3367834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 7].length) (baseStart_3367834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3367834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3367834 prefixEnd_3367834 := by exact prefixLift 3367834
  have htrace : WordTrace (prefixWord ++ tailWord_3367834) baseStart_3367834 baseEnd_3367834 := by
    simpa [prefixWord, tailWord_3367834, baseEnd_3367834] using wordTrace_append hprefix tailTrace_3367834
  have hstable : (prefixWord ++ tailWord_3367834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367834).length < 2 ^ (prefixWord ++ tailWord_3367834).sum := by decide
  have hdescent : baseEnd_3367834 < baseStart_3367834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367853 : List Nat := [1, 5, 2, 3, 2, 1, 1, 1, 2, 4]
def baseStart_3367853 : Nat := 118140960795 + 3367853 * 2 ^ 59
def prefixEnd_3367853 : Nat := 4983230072969 + 3 ^ 40 * 3367853 * 2
def baseEnd_3367853 : Nat := 1152884908457811328899355

theorem tailTrace_3367853 : CollatzResearch.WordTrace tailWord_3367853 prefixEnd_3367853 1152884908457811328899355 := by
  unfold tailWord_3367853
  simp only [CollatzResearch.WordTrace]
  refine ⟨122835690267851239344812213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81890460178567492896541475 122835690267851239344812213)
  ·
    refine ⟨11515845962611053688576145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 122835690267851239344812213 11515845962611053688576145)
    ·
      refine ⟨8636884471958290266432109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11515845962611053688576145 8636884471958290266432109)
      ·
        refine ⟨3238831676984358849912041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8636884471958290266432109 3238831676984358849912041)
        ·
          refine ⟨2429123757738269137434031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3238831676984358849912041 2429123757738269137434031)
          ·
            refine ⟨3643685636607403706151047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2429123757738269137434031 3643685636607403706151047)
            ·
              refine ⟨5465528454911105559226571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3643685636607403706151047 5465528454911105559226571)
              ·
                refine ⟨8198292682366658338839857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5465528454911105559226571 8198292682366658338839857)
                ·
                  refine ⟨6148719511774993754129893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8198292682366658338839857 6148719511774993754129893)
                  ·
                    refine ⟨1152884908457811328899355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6148719511774993754129893 1152884908457811328899355)
                    ·
                      rfl

theorem cell22_3367853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_3367853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3367853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3367853 prefixEnd_3367853 := by exact prefixLift 3367853
  have htrace : WordTrace (prefixWord ++ tailWord_3367853) baseStart_3367853 baseEnd_3367853 := by
    simpa [prefixWord, tailWord_3367853, baseEnd_3367853] using wordTrace_append hprefix tailTrace_3367853
  have hstable : (prefixWord ++ tailWord_3367853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367853).length < 2 ^ (prefixWord ++ tailWord_3367853).sum := by decide
  have hdescent : baseEnd_3367853 < baseStart_3367853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367894 : List Nat := [5, 2, 1, 1, 2, 1, 2, 1, 2, 5]
def baseStart_3367894 : Nat := 118140960795 + 3367894 * 2 ^ 59
def prefixEnd_3367894 : Nat := 4983230072969 + 3 ^ 40 * 3367894 * 2
def baseEnd_3367894 : Nat := 1152898943595700888624229

theorem tailTrace_3367894 : CollatzResearch.WordTrace tailWord_3367894 prefixEnd_3367894 1152898943595700888624229 := by
  unfold tailWord_3367894
  simp only [CollatzResearch.WordTrace]
  refine ⟨7677324103793918959190921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81891457107135135564703157 7677324103793918959190921)
  ·
    refine ⟨5757993077845439219393191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7677324103793918959190921 5757993077845439219393191)
    ·
      refine ⟨8636989616768158829089787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5757993077845439219393191 8636989616768158829089787)
      ·
        refine ⟨12955484425152238243634681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8636989616768158829089787 12955484425152238243634681)
        ·
          refine ⟨9716613318864178682726011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12955484425152238243634681 9716613318864178682726011)
          ·
            refine ⟨14574919978296268024089017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9716613318864178682726011 14574919978296268024089017)
            ·
              refine ⟨10931189983722201018066763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14574919978296268024089017 10931189983722201018066763)
              ·
                refine ⟨16396784975583301527100145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10931189983722201018066763 16396784975583301527100145)
                ·
                  refine ⟨12297588731687476145325109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16396784975583301527100145 12297588731687476145325109)
                  ·
                    refine ⟨1152898943595700888624229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12297588731687476145325109 1152898943595700888624229)
                    ·
                      rfl

theorem cell22_3367894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_3367894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3367894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3367894 prefixEnd_3367894 := by exact prefixLift 3367894
  have htrace : WordTrace (prefixWord ++ tailWord_3367894) baseStart_3367894 baseEnd_3367894 := by
    simpa [prefixWord, tailWord_3367894, baseEnd_3367894] using wordTrace_append hprefix tailTrace_3367894
  have hstable : (prefixWord ++ tailWord_3367894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367894).length < 2 ^ (prefixWord ++ tailWord_3367894).sum := by decide
  have hdescent : baseEnd_3367894 < baseStart_3367894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367937 : List Nat := [1, 2, 4, 1, 2, 2, 1, 1, 4, 4]
def baseStart_3367937 : Nat := 118140960795 + 3367937 * 2 ^ 59
def prefixEnd_3367937 : Nat := 4983230072969 + 3 ^ 40 * 3367937 * 2
def baseEnd_3367937 : Nat := 1152913663374463109799097

theorem tailTrace_3367937 : CollatzResearch.WordTrace tailWord_3367937 prefixEnd_3367937 1152913663374463109799097 := by
  unfold tailWord_3367937
  simp only [CollatzResearch.WordTrace]
  refine ⟨122838753999546921690870065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81892502666364614460580043 122838753999546921690870065)
  ·
    refine ⟨92129065499660191268152549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122838753999546921690870065 92129065499660191268152549)
    ·
      refine ⟨17274199781186285862778603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92129065499660191268152549 17274199781186285862778603)
      ·
        refine ⟨25911299671779428794167905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17274199781186285862778603 25911299671779428794167905)
        ·
          refine ⟨19433474753834571595625929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25911299671779428794167905 19433474753834571595625929)
          ·
            refine ⟨14575106065375928696719447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19433474753834571595625929 14575106065375928696719447)
            ·
              refine ⟨21862659098063893045079171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14575106065375928696719447 21862659098063893045079171)
              ·
                refine ⟨32793988647095839567618757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21862659098063893045079171 32793988647095839567618757)
                ·
                  refine ⟨6148872871330469918928517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32793988647095839567618757 6148872871330469918928517)
                  ·
                    refine ⟨1152913663374463109799097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6148872871330469918928517 1152913663374463109799097)
                    ·
                      rfl

theorem cell22_3367937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_3367937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3367937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3367937 prefixEnd_3367937 := by exact prefixLift 3367937
  have htrace : WordTrace (prefixWord ++ tailWord_3367937) baseStart_3367937 baseEnd_3367937 := by
    simpa [prefixWord, tailWord_3367937, baseEnd_3367937] using wordTrace_append hprefix tailTrace_3367937
  have hstable : (prefixWord ++ tailWord_3367937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367937).length < 2 ^ (prefixWord ++ tailWord_3367937).sum := by decide
  have hdescent : baseEnd_3367937 < baseStart_3367937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368044 : List Nat := [2, 2, 1, 1, 3, 2, 3, 3, 1, 4]
def baseStart_3368044 : Nat := 118140960795 + 3368044 * 2 ^ 59
def prefixEnd_3368044 : Nat := 4983230072969 + 3 ^ 40 * 3368044 * 2
def baseEnd_3368044 : Nat := 1152950291661150497373769

theorem tailTrace_3368044 : CollatzResearch.WordTrace tailWord_3368044 prefixEnd_3368044 1152950291661150497373769 := by
  unfold tailWord_3368044
  simp only [CollatzResearch.WordTrace]
  refine ⟨61421328305079639482507593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81895104406772852643343457 61421328305079639482507593)
  ·
    refine ⟨46065996228809729611880695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61421328305079639482507593 46065996228809729611880695)
    ·
      refine ⟨69098994343214594417821043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46065996228809729611880695 69098994343214594417821043)
      ·
        refine ⟨103648491514821891626731565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69098994343214594417821043 103648491514821891626731565)
        ·
          refine ⟨38868184318058209360024337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103648491514821891626731565 38868184318058209360024337)
          ·
            refine ⟨29151138238543657020018253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38868184318058209360024337 29151138238543657020018253)
            ·
              refine ⟨10931676839453871382506845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29151138238543657020018253 10931676839453871382506845)
              ·
                refine ⟨4099378814795201768440067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10931676839453871382506845 4099378814795201768440067)
                ·
                  refine ⟨6149068222192802652660101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4099378814795201768440067 6149068222192802652660101)
                  ·
                    refine ⟨1152950291661150497373769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6149068222192802652660101 1152950291661150497373769)
                    ·
                      rfl

theorem cell22_3368044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 4].length) (baseStart_3368044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3368044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3368044 prefixEnd_3368044 := by exact prefixLift 3368044
  have htrace : WordTrace (prefixWord ++ tailWord_3368044) baseStart_3368044 baseEnd_3368044 := by
    simpa [prefixWord, tailWord_3368044, baseEnd_3368044] using wordTrace_append hprefix tailTrace_3368044
  have hstable : (prefixWord ++ tailWord_3368044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368044).length < 2 ^ (prefixWord ++ tailWord_3368044).sum := by decide
  have hdescent : baseEnd_3368044 < baseStart_3368044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368106 : List Nat := [3, 1, 5, 1, 1, 1, 1, 1, 4, 4]
def baseStart_3368106 : Nat := 118140960795 + 3368106 * 2 ^ 59
def prefixEnd_3368106 : Nat := 4983230072969 + 3 ^ 40 * 3368106 * 2
def baseEnd_3368106 : Nat := 1152971515528203002323579

theorem tailTrace_3368106 : CollatzResearch.WordTrace tailWord_3368106 prefixEnd_3368106 1152971515528203002323579 := by
  unfold tailWord_3368106
  simp only [CollatzResearch.WordTrace]
  refine ⟨30711229483983665888443043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81896611957289775702514781 30711229483983665888443043)
  ·
    refine ⟨46066844225975498832664565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30711229483983665888443043 46066844225975498832664565)
    ·
      refine ⟨4318766646185203015562303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46066844225975498832664565 4318766646185203015562303)
      ·
        refine ⟨6478149969277804523343455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4318766646185203015562303 6478149969277804523343455)
        ·
          refine ⟨9717224953916706785015183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6478149969277804523343455 9717224953916706785015183)
          ·
            refine ⟨14575837430875060177522775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9717224953916706785015183 14575837430875060177522775)
            ·
              refine ⟨21863756146312590266284163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14575837430875060177522775 21863756146312590266284163)
              ·
                refine ⟨32795634219468885399426245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21863756146312590266284163 32795634219468885399426245)
                ·
                  refine ⟨6149181416150416012392421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32795634219468885399426245 6149181416150416012392421)
                  ·
                    refine ⟨1152971515528203002323579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6149181416150416012392421 1152971515528203002323579)
                    ·
                      rfl

theorem cell22_3368106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_3368106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3368106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3368106 prefixEnd_3368106 := by exact prefixLift 3368106
  have htrace : WordTrace (prefixWord ++ tailWord_3368106) baseStart_3368106 baseEnd_3368106 := by
    simpa [prefixWord, tailWord_3368106, baseEnd_3368106] using wordTrace_append hprefix tailTrace_3368106
  have hstable : (prefixWord ++ tailWord_3368106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368106).length < 2 ^ (prefixWord ++ tailWord_3368106).sum := by decide
  have hdescent : baseEnd_3368106 < baseStart_3368106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368147 : List Nat := [1, 1, 1, 2, 1, 1, 1, 6, 1, 7]
def baseStart_3368147 : Nat := 118140960795 + 3368147 * 2 ^ 59
def prefixEnd_3368147 : Nat := 4983230072969 + 3 ^ 40 * 3368147 * 2
def baseEnd_3368147 : Nat := 1152985550666092562048453

theorem tailTrace_3368147 : CollatzResearch.WordTrace tailWord_3368147 prefixEnd_3368147 1152985550666092562048453 := by
  unfold tailWord_3368147
  simp only [CollatzResearch.WordTrace]
  refine ⟨122846413328786127556014695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81897608885857418370676463 122846413328786127556014695)
  ·
    refine ⟨184269619993179191334022043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122846413328786127556014695 184269619993179191334022043)
    ·
      refine ⟨276404429989768787001033065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184269619993179191334022043 276404429989768787001033065)
      ·
        refine ⟨207303322492326590250774799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276404429989768787001033065 207303322492326590250774799)
        ·
          refine ⟨310954983738489885376162199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207303322492326590250774799 310954983738489885376162199)
          ·
            refine ⟨466432475607734828064243299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310954983738489885376162199 466432475607734828064243299)
            ·
              refine ⟨699648713411602242096364949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 466432475607734828064243299 699648713411602242096364949)
              ·
                refine ⟨32796033441168855098267107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 699648713411602242096364949 32796033441168855098267107)
                ·
                  refine ⟨49194050161753282647400661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32796033441168855098267107 49194050161753282647400661)
                  ·
                    refine ⟨1152985550666092562048453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49194050161753282647400661 1152985550666092562048453)
                    ·
                      rfl

theorem cell22_3368147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 7].length) (baseStart_3368147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3368147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3368147 prefixEnd_3368147 := by exact prefixLift 3368147
  have htrace : WordTrace (prefixWord ++ tailWord_3368147) baseStart_3368147 baseEnd_3368147 := by
    simpa [prefixWord, tailWord_3368147, baseEnd_3368147] using wordTrace_append hprefix tailTrace_3368147
  have hstable : (prefixWord ++ tailWord_3368147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368147).length < 2 ^ (prefixWord ++ tailWord_3368147).sum := by decide
  have hdescent : baseEnd_3368147 < baseStart_3368147 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368170 : List Nat := [3, 1, 3, 1, 1, 3, 4, 2, 1, 3]
def baseStart_3368170 : Nat := 118140960795 + 3368170 * 2 ^ 59
def prefixEnd_3368170 : Nat := 4983230072969 + 3 ^ 40 * 3368170 * 2
def baseEnd_3368170 : Nat := 1152993424036128168723383

theorem tailTrace_3368170 : CollatzResearch.WordTrace tailWord_3368170 prefixEnd_3368170 1152993424036128168723383 := by
  unfold tailWord_3368170
  simp only [CollatzResearch.WordTrace]
  refine ⟨30711813051925700621025491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81898168138468534989401309 30711813051925700621025491)
  ·
    refine ⟨46067719577888550931538237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30711813051925700621025491 46067719577888550931538237)
    ·
      refine ⟨17275394841708206599326839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46067719577888550931538237 17275394841708206599326839)
      ·
        refine ⟨25913092262562309898990259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17275394841708206599326839 25913092262562309898990259)
        ·
          refine ⟨38869638393843464848485389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25913092262562309898990259 38869638393843464848485389)
          ·
            refine ⟨14576114397691299318182021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38869638393843464848485389 14576114397691299318182021)
            ·
              refine ⟨2733021449567118622159129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14576114397691299318182021 2733021449567118622159129)
              ·
                refine ⟨2049766087175338966619347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2733021449567118622159129 2049766087175338966619347)
                ·
                  refine ⟨3074649130763008449929021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2049766087175338966619347 3074649130763008449929021)
                  ·
                    refine ⟨1152993424036128168723383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3074649130763008449929021 1152993424036128168723383)
                    ·
                      rfl

theorem cell22_3368170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4, 2, 1, 3].length) (baseStart_3368170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3368170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3368170 prefixEnd_3368170 := by exact prefixLift 3368170
  have htrace : WordTrace (prefixWord ++ tailWord_3368170) baseStart_3368170 baseEnd_3368170 := by
    simpa [prefixWord, tailWord_3368170, baseEnd_3368170] using wordTrace_append hprefix tailTrace_3368170
  have hstable : (prefixWord ++ tailWord_3368170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368170).length < 2 ^ (prefixWord ++ tailWord_3368170).sum := by decide
  have hdescent : baseEnd_3368170 < baseStart_3368170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368179 : List Nat := [1, 1, 1, 2, 2, 5, 1, 2, 3, 4]
def baseStart_3368179 : Nat := 118140960795 + 3368179 * 2 ^ 59
def prefixEnd_3368179 : Nat := 4983230072969 + 3 ^ 40 * 3368179 * 2
def baseEnd_3368179 : Nat := 1152996504920055145248355

theorem tailTrace_3368179 : CollatzResearch.WordTrace tailWord_3368179 prefixEnd_3368179 1152996504920055145248355 := by
  unfold tailWord_3368179
  simp only [CollatzResearch.WordTrace]
  refine ⟨122847580464670197021179591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81898386976446798014119727 122847580464670197021179591)
  ·
    refine ⟨184271370697005295531769387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122847580464670197021179591 184271370697005295531769387)
    ·
      refine ⟨276407056045507943297654081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184271370697005295531769387 276407056045507943297654081)
      ·
        refine ⟨207305292034130957473240561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276407056045507943297654081 207305292034130957473240561)
        ·
          refine ⟨155478969025598218104930421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207305292034130957473240561 155478969025598218104930421)
          ·
            refine ⟨14576153346149832947337227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 155478969025598218104930421 14576153346149832947337227)
            ·
              refine ⟨21864230019224749421005841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14576153346149832947337227 21864230019224749421005841)
              ·
                refine ⟨16398172514418562065754381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21864230019224749421005841 16398172514418562065754381)
                ·
                  refine ⟨6149314692906960774657893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16398172514418562065754381 6149314692906960774657893)
                  ·
                    refine ⟨1152996504920055145248355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6149314692906960774657893 1152996504920055145248355)
                    ·
                      rfl

theorem cell22_3368179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 3, 4].length) (baseStart_3368179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3368179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3368179 prefixEnd_3368179 := by exact prefixLift 3368179
  have htrace : WordTrace (prefixWord ++ tailWord_3368179) baseStart_3368179 baseEnd_3368179 := by
    simpa [prefixWord, tailWord_3368179, baseEnd_3368179] using wordTrace_append hprefix tailTrace_3368179
  have hstable : (prefixWord ++ tailWord_3368179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368179).length < 2 ^ (prefixWord ++ tailWord_3368179).sum := by decide
  have hdescent : baseEnd_3368179 < baseStart_3368179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368196 : List Nat := [2, 3, 2, 2, 2, 1, 2, 1, 3, 4]
def baseStart_3368196 : Nat := 118140960795 + 3368196 * 2 ^ 59
def prefixEnd_3368196 : Nat := 4983230072969 + 3 ^ 40 * 3368196 * 2
def baseEnd_3368196 : Nat := 1153002324367472767573303

theorem tailTrace_3368196 : CollatzResearch.WordTrace tailWord_3368196 prefixEnd_3368196 1153002324367472767573303 := by
  unfold tailWord_3368196
  simp only [CollatzResearch.WordTrace]
  refine ⟨61424100252804304462274221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81898800337072405949698961 61424100252804304462274221)
  ·
    refine ⟨23034037594801614173352833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61424100252804304462274221 23034037594801614173352833)
    ·
      refine ⟨17275528196101210630014625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23034037594801614173352833 17275528196101210630014625)
      ·
        refine ⟨12956646147075907972510969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17275528196101210630014625 12956646147075907972510969)
        ·
          refine ⟨9717484610306930979383227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12956646147075907972510969 9717484610306930979383227)
          ·
            refine ⟨14576226915460396469074841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9717484610306930979383227 14576226915460396469074841)
            ·
              refine ⟨10932170186595297351806131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14576226915460396469074841 10932170186595297351806131)
              ·
                refine ⟨16398255279892946027709197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10932170186595297351806131 16398255279892946027709197)
                ·
                  refine ⟨6149345729959854760390949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16398255279892946027709197 6149345729959854760390949)
                  ·
                    refine ⟨1153002324367472767573303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6149345729959854760390949 1153002324367472767573303)
                    ·
                      rfl

theorem cell22_3368196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_3368196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3368196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3368196 prefixEnd_3368196 := by exact prefixLift 3368196
  have htrace : WordTrace (prefixWord ++ tailWord_3368196) baseStart_3368196 baseEnd_3368196 := by
    simpa [prefixWord, tailWord_3368196, baseEnd_3368196] using wordTrace_append hprefix tailTrace_3368196
  have hstable : (prefixWord ++ tailWord_3368196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368196).length < 2 ^ (prefixWord ++ tailWord_3368196).sum := by decide
  have hdescent : baseEnd_3368196 < baseStart_3368196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368209 : List Nat := [1, 2, 2, 1, 1, 4, 1, 4, 1, 5]
def baseStart_3368209 : Nat := 118140960795 + 3368209 * 2 ^ 59
def prefixEnd_3368209 : Nat := 4983230072969 + 3 ^ 40 * 3368209 * 2
def baseEnd_3368209 : Nat := 1153006774533145066998263

theorem tailTrace_3368209 : CollatzResearch.WordTrace tailWord_3368209 prefixEnd_3368209 1153006774533145066998263 := by
  unfold tailWord_3368209
  simp only [CollatzResearch.WordTrace]
  refine ⟨122848674654561512144771681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81899116436374341429847787 122848674654561512144771681)
  ·
    refine ⟨92136505990921134108578761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122848674654561512144771681 92136505990921134108578761)
    ·
      refine ⟨69102379493190850581434071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92136505990921134108578761 69102379493190850581434071)
      ·
        refine ⟨103653569239786275872151107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69102379493190850581434071 103653569239786275872151107)
        ·
          refine ⟨155480353859679413808226661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103653569239786275872151107 155480353859679413808226661)
          ·
            refine ⟨29152566348689890089042499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155480353859679413808226661 29152566348689890089042499)
            ·
              refine ⟨43728849523034835133563749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29152566348689890089042499 43728849523034835133563749)
              ·
                refine ⟨8199159285569031587543203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43728849523034835133563749 8199159285569031587543203)
                ·
                  refine ⟨12298738928353547381314805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8199159285569031587543203 12298738928353547381314805)
                  ·
                    refine ⟨1153006774533145066998263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12298738928353547381314805 1153006774533145066998263)
                    ·
                      rfl

theorem cell22_3368209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 5].length) (baseStart_3368209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3368209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3368209 prefixEnd_3368209 := by exact prefixLift 3368209
  have htrace : WordTrace (prefixWord ++ tailWord_3368209) baseStart_3368209 baseEnd_3368209 := by
    simpa [prefixWord, tailWord_3368209, baseEnd_3368209] using wordTrace_append hprefix tailTrace_3368209
  have hstable : (prefixWord ++ tailWord_3368209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368209).length < 2 ^ (prefixWord ++ tailWord_3368209).sum := by decide
  have hdescent : baseEnd_3368209 < baseStart_3368209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368288 : List Nat := [2, 1, 1, 3, 4, 1, 3, 1, 3, 3]
def baseStart_3368288 : Nat := 118140960795 + 3368288 * 2 ^ 59
def prefixEnd_3368288 : Nat := 4983230072969 + 3 ^ 40 * 3368288 * 2
def baseEnd_3368288 : Nat := 1153033817847615194273021

theorem tailTrace_3368288 : CollatzResearch.WordTrace tailWord_3368288 prefixEnd_3368288 1153033817847615194273021 := by
  unfold tailWord_3368288
  simp only [CollatzResearch.WordTrace]
  refine ⟨61425778010637654318448759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81901037347516872424598345 61425778010637654318448759)
  ·
    refine ⟨92138667015956481477673139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61425778010637654318448759 92138667015956481477673139)
    ·
      refine ⟨138208000523934722216509709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92138667015956481477673139 138208000523934722216509709)
      ·
        refine ⟨51828000196475520831191141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138208000523934722216509709 51828000196475520831191141)
        ·
          refine ⟨9717750036839160155848339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51828000196475520831191141 9717750036839160155848339)
          ·
            refine ⟨14576625055258740233772509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9717750036839160155848339 14576625055258740233772509)
            ·
              refine ⟨5466234395722027587664691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14576625055258740233772509 5466234395722027587664691)
              ·
                refine ⟨8199351593583041381497037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5466234395722027587664691 8199351593583041381497037)
                ·
                  refine ⟨3074756847593640518061389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8199351593583041381497037 3074756847593640518061389)
                  ·
                    refine ⟨1153033817847615194273021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3074756847593640518061389 1153033817847615194273021)
                    ·
                      rfl

theorem cell22_3368288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 1, 3, 3].length) (baseStart_3368288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3368288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3368288 prefixEnd_3368288 := by exact prefixLift 3368288
  have htrace : WordTrace (prefixWord ++ tailWord_3368288) baseStart_3368288 baseEnd_3368288 := by
    simpa [prefixWord, tailWord_3368288, baseEnd_3368288] using wordTrace_append hprefix tailTrace_3368288
  have hstable : (prefixWord ++ tailWord_3368288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368288).length < 2 ^ (prefixWord ++ tailWord_3368288).sum := by decide
  have hdescent : baseEnd_3368288 < baseStart_3368288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368314 : List Nat := [3, 1, 1, 1, 1, 1, 2, 2, 2, 8]
def baseStart_3368314 : Nat := 118140960795 + 3368314 * 2 ^ 59
def prefixEnd_3368314 : Nat := 4983230072969 + 3 ^ 40 * 3368314 * 2
def baseEnd_3368314 : Nat := 1153042718178959793122941

theorem tailTrace_3368314 : CollatzResearch.WordTrace tailWord_3368314 prefixEnd_3368314 1153042718178959793122941 := by
  unfold tailWord_3368314
  simp only [CollatzResearch.WordTrace]
  refine ⟨30713126079795278769335999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81901669546120743384895997 30713126079795278769335999)
  ·
    refine ⟨46069689119692918154003999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30713126079795278769335999 46069689119692918154003999)
    ·
      refine ⟨69104533679539377231005999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46069689119692918154003999 69104533679539377231005999)
      ·
        refine ⟨103656800519309065846508999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69104533679539377231005999 103656800519309065846508999)
        ·
          refine ⟨155485200778963598769763499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103656800519309065846508999 155485200778963598769763499)
          ·
            refine ⟨233227801168445398154645249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155485200778963598769763499 233227801168445398154645249)
            ·
              refine ⟨174920850876334048615983937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 233227801168445398154645249 174920850876334048615983937)
              ·
                refine ⟨131190638157250536461987953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174920850876334048615983937 131190638157250536461987953)
                ·
                  refine ⟨98392978617937902346490965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131190638157250536461987953 98392978617937902346490965)
                  ·
                    refine ⟨1153042718178959793122941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 98392978617937902346490965 1153042718178959793122941)
                    ·
                      rfl

theorem cell22_3368314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 2, 8].length) (baseStart_3368314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3368314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3368314 prefixEnd_3368314 := by exact prefixLift 3368314
  have htrace : WordTrace (prefixWord ++ tailWord_3368314) baseStart_3368314 baseEnd_3368314 := by
    simpa [prefixWord, tailWord_3368314, baseEnd_3368314] using wordTrace_append hprefix tailTrace_3368314
  have hstable : (prefixWord ++ tailWord_3368314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368314).length < 2 ^ (prefixWord ++ tailWord_3368314).sum := by decide
  have hdescent : baseEnd_3368314 < baseStart_3368314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368346 : List Nat := [3, 1, 1, 4, 1, 1, 2, 3, 6]
def baseStart_3368346 : Nat := 118140960795 + 3368346 * 2 ^ 59
def prefixEnd_3368346 : Nat := 4983230072969 + 3 ^ 40 * 3368346 * 2
def baseEnd_3368346 : Nat := 384351224144307458774281

theorem tailTrace_3368346 : CollatzResearch.WordTrace tailWord_3368346 prefixEnd_3368346 384351224144307458774281 := by
  unfold tailWord_3368346
  simp only [CollatzResearch.WordTrace]
  refine ⟨30713417863766296135627223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81902447636710123028339261 30713417863766296135627223)
  ·
    refine ⟨46070126795649444203440835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30713417863766296135627223 46070126795649444203440835)
    ·
      refine ⟨69105190193474166305161253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46070126795649444203440835 69105190193474166305161253)
      ·
        refine ⟨12957223161276406182217735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69105190193474166305161253 12957223161276406182217735)
        ·
          refine ⟨19435834741914609273326603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12957223161276406182217735 19435834741914609273326603)
          ·
            refine ⟨29153752112871913909989905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19435834741914609273326603 29153752112871913909989905)
            ·
              refine ⟨21865314084653935432492429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29153752112871913909989905 21865314084653935432492429)
              ·
                refine ⟨8199492781745225787184661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21865314084653935432492429 8199492781745225787184661)
                ·
                  refine ⟨384351224144307458774281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8199492781745225787184661 384351224144307458774281)
                  ·
                    rfl

theorem cell22_3368346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 3, 6].length) (baseStart_3368346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3368346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3368346 prefixEnd_3368346 := by exact prefixLift 3368346
  have htrace : WordTrace (prefixWord ++ tailWord_3368346) baseStart_3368346 baseEnd_3368346 := by
    simpa [prefixWord, tailWord_3368346, baseEnd_3368346] using wordTrace_append hprefix tailTrace_3368346
  have hstable : (prefixWord ++ tailWord_3368346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368346).length < 2 ^ (prefixWord ++ tailWord_3368346).sum := by decide
  have hdescent : baseEnd_3368346 < baseStart_3368346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368350 : List Nat := [4, 3, 1, 2, 2, 1, 1, 1, 2, 5]
def baseStart_3368350 : Nat := 118140960795 + 3368350 * 2 ^ 59
def prefixEnd_3368350 : Nat := 4983230072969 + 3 ^ 40 * 3368350 * 2
def baseEnd_3368350 : Nat := 1153055041714667699222831

theorem tailTrace_3368350 : CollatzResearch.WordTrace tailWord_3368350 prefixEnd_3368350 1153055041714667699222831 := by
  unfold tailWord_3368350
  simp only [CollatzResearch.WordTrace]
  refine ⟨15356727168381336653206813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81902544898033795483769669 15356727168381336653206813)
  ·
    refine ⟨5758772688143001244952555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15356727168381336653206813 5758772688143001244952555)
    ·
      refine ⟨8638159032214501867428833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5758772688143001244952555 8638159032214501867428833)
      ·
        refine ⟨6478619274160876400571625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8638159032214501867428833 6478619274160876400571625)
        ·
          refine ⟨4858964455620657300428719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6478619274160876400571625 4858964455620657300428719)
          ·
            refine ⟨7288446683430985950643079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4858964455620657300428719 7288446683430985950643079)
            ·
              refine ⟨10932670025146478925964619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7288446683430985950643079 10932670025146478925964619)
              ·
                refine ⟨16399005037719718388946929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10932670025146478925964619 16399005037719718388946929)
                ·
                  refine ⟨12299253778289788791710197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16399005037719718388946929 12299253778289788791710197)
                  ·
                    refine ⟨1153055041714667699222831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12299253778289788791710197 1153055041714667699222831)
                    ·
                      rfl

theorem cell22_3368350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_3368350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3368350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3368350 prefixEnd_3368350 := by exact prefixLift 3368350
  have htrace : WordTrace (prefixWord ++ tailWord_3368350) baseStart_3368350 baseEnd_3368350 := by
    simpa [prefixWord, tailWord_3368350, baseEnd_3368350] using wordTrace_append hprefix tailTrace_3368350
  have hstable : (prefixWord ++ tailWord_3368350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368350).length < 2 ^ (prefixWord ++ tailWord_3368350).sum := by decide
  have hdescent : baseEnd_3368350 < baseStart_3368350 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368361 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 8, 3]
def baseStart_3368361 : Nat := 118140960795 + 3368361 * 2 ^ 59
def prefixEnd_3368361 : Nat := 4983230072969 + 3 ^ 40 * 3368361 * 2
def baseEnd_3368361 : Nat := 1153058807239467337197797

theorem tailTrace_3368361 : CollatzResearch.WordTrace tailWord_3368361 prefixEnd_3368361 1153058807239467337197797 := by
  unfold tailWord_3368361
  simp only [CollatzResearch.WordTrace]
  refine ⟨122854218550010842104304937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81902812366673894736203291 122854218550010842104304937)
  ·
    refine ⟨92140663912508131578228703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122854218550010842104304937 92140663912508131578228703)
    ·
      refine ⟨138210995868762197367343055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92140663912508131578228703 138210995868762197367343055)
      ·
        refine ⟨207316493803143296051014583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138210995868762197367343055 207316493803143296051014583)
        ·
          refine ⟨310974740704714944076521875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207316493803143296051014583 310974740704714944076521875)
          ·
            refine ⟨466462111057072416114782813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310974740704714944076521875 466462111057072416114782813)
            ·
              refine ⟨174923291646402156043043555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 466462111057072416114782813 174923291646402156043043555)
              ·
                refine ⟨262384937469603234064565333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174923291646402156043043555 262384937469603234064565333)
                ·
                  refine ⟨3074823485971912899194125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 262384937469603234064565333 3074823485971912899194125)
                  ·
                    refine ⟨1153058807239467337197797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3074823485971912899194125 1153058807239467337197797)
                    ·
                      rfl

theorem cell22_3368361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 8, 3].length) (baseStart_3368361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3368361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3368361 prefixEnd_3368361 := by exact prefixLift 3368361
  have htrace : WordTrace (prefixWord ++ tailWord_3368361) baseStart_3368361 baseEnd_3368361 := by
    simpa [prefixWord, tailWord_3368361, baseEnd_3368361] using wordTrace_append hprefix tailTrace_3368361
  have hstable : (prefixWord ++ tailWord_3368361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368361).length < 2 ^ (prefixWord ++ tailWord_3368361).sum := by decide
  have hdescent : baseEnd_3368361 < baseStart_3368361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368386 : List Nat := [3, 5, 2, 1, 1, 2, 1, 2, 5]
def baseStart_3368386 : Nat := 118140960795 + 3368386 * 2 ^ 59
def prefixEnd_3368386 : Nat := 4983230072969 + 3 ^ 40 * 3368386 * 2
def baseEnd_3368386 : Nat := 384355788416791868440907

theorem tailTrace_3368386 : CollatzResearch.WordTrace tailWord_3368386 prefixEnd_3368386 384355788416791868440907 := by
  unfold tailWord_3368386
  simp only [CollatzResearch.WordTrace]
  refine ⟨30713782593730067843491253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81903420249946847582643341 30713782593730067843491253)
  ·
    refine ⟨2879417118162193860327305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30713782593730067843491253 2879417118162193860327305)
    ·
      refine ⟨2159562838621645395245479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2879417118162193860327305 2159562838621645395245479)
      ·
        refine ⟨3239344257932468092868219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2159562838621645395245479 3239344257932468092868219)
        ·
          refine ⟨4859016386898702139302329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3239344257932468092868219 4859016386898702139302329)
          ·
            refine ⟨3644262290174026604476747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4859016386898702139302329 3644262290174026604476747)
            ·
              refine ⟨5466393435261039906715121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3644262290174026604476747 5466393435261039906715121)
              ·
                refine ⟨4099795076445779930036341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5466393435261039906715121 4099795076445779930036341)
                ·
                  refine ⟨384355788416791868440907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4099795076445779930036341 384355788416791868440907)
                  ·
                    rfl

theorem cell22_3368386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_3368386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3368386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3368386 prefixEnd_3368386 := by exact prefixLift 3368386
  have htrace : WordTrace (prefixWord ++ tailWord_3368386) baseStart_3368386 baseEnd_3368386 := by
    simpa [prefixWord, tailWord_3368386, baseEnd_3368386] using wordTrace_append hprefix tailTrace_3368386
  have hstable : (prefixWord ++ tailWord_3368386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368386).length < 2 ^ (prefixWord ++ tailWord_3368386).sum := by decide
  have hdescent : baseEnd_3368386 < baseStart_3368386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368451 : List Nat := [1, 1, 1, 3, 2, 1, 2, 4, 2, 5]
def baseStart_3368451 : Nat := 118140960795 + 3368451 * 2 ^ 59
def prefixEnd_3368451 : Nat := 4983230072969 + 3 ^ 40 * 3368451 * 2
def baseEnd_3368451 : Nat := 1153089616078737102447521

theorem tailTrace_3368451 : CollatzResearch.WordTrace tailWord_3368451 prefixEnd_3368451 1153089616078737102447521 := by
  unfold tailWord_3368451
  simp only [CollatzResearch.WordTrace]
  refine ⟨122857501119684787475081207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81905000746456524983387471 122857501119684787475081207)
  ·
    refine ⟨184286251679527181212621811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122857501119684787475081207 184286251679527181212621811)
    ·
      refine ⟨276429377519290771818932717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184286251679527181212621811 276429377519290771818932717)
      ·
        refine ⟨103661016569734039432099769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 276429377519290771818932717 103661016569734039432099769)
        ·
          refine ⟨77745762427300529574074827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103661016569734039432099769 77745762427300529574074827)
          ·
            refine ⟨116618643640950794361112241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77745762427300529574074827 116618643640950794361112241)
            ·
              refine ⟨87463982730713095770834181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116618643640950794361112241 87463982730713095770834181)
              ·
                refine ⟨16399496762008705457031409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87463982730713095770834181 16399496762008705457031409)
                ·
                  refine ⟨12299622571506529092773557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16399496762008705457031409 12299622571506529092773557)
                  ·
                    refine ⟨1153089616078737102447521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12299622571506529092773557 1153089616078737102447521)
                    ·
                      rfl

theorem cell22_3368451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 2, 5].length) (baseStart_3368451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3368451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3368451 prefixEnd_3368451 := by exact prefixLift 3368451
  have htrace : WordTrace (prefixWord ++ tailWord_3368451) baseStart_3368451 baseEnd_3368451 := by
    simpa [prefixWord, tailWord_3368451, baseEnd_3368451] using wordTrace_append hprefix tailTrace_3368451
  have hstable : (prefixWord ++ tailWord_3368451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368451).length < 2 ^ (prefixWord ++ tailWord_3368451).sum := by decide
  have hdescent : baseEnd_3368451 < baseStart_3368451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368457 : List Nat := [1, 2, 1, 1, 3, 1, 7, 2, 1, 3]
def baseStart_3368457 : Nat := 118140960795 + 3368457 * 2 ^ 59
def prefixEnd_3368457 : Nat := 4983230072969 + 3 ^ 40 * 3368457 * 2
def baseEnd_3368457 : Nat := 1153091670001355086797503

theorem tailTrace_3368457 : CollatzResearch.WordTrace tailWord_3368457 prefixEnd_3368457 1153091670001355086797503 := by
  unfold tailWord_3368457
  simp only [CollatzResearch.WordTrace]
  refine ⟨122857719957663050499799625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81905146638442033666533083 122857719957663050499799625)
  ·
    refine ⟨92143289968247287874849719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122857719957663050499799625 92143289968247287874849719)
    ·
      refine ⟨138214934952370931812274579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92143289968247287874849719 138214934952370931812274579)
      ·
        refine ⟨207322402428556397718411869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138214934952370931812274579 207322402428556397718411869)
        ·
          refine ⟨77745900910708649144404451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207322402428556397718411869 77745900910708649144404451)
          ·
            refine ⟨116618851366062973716606677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77745900910708649144404451 116618851366062973716606677)
            ·
              refine ⟨2733254328892100946482969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 116618851366062973716606677 2733254328892100946482969)
              ·
                refine ⟨2049940746669075709862227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2733254328892100946482969 2049940746669075709862227)
                ·
                  refine ⟨3074911120003613564793341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2049940746669075709862227 3074911120003613564793341)
                  ·
                    refine ⟨1153091670001355086797503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3074911120003613564793341 1153091670001355086797503)
                    ·
                      rfl

theorem cell22_3368457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7, 2, 1, 3].length) (baseStart_3368457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3368457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3368457 prefixEnd_3368457 := by exact prefixLift 3368457
  have htrace : WordTrace (prefixWord ++ tailWord_3368457) baseStart_3368457 baseEnd_3368457 := by
    simpa [prefixWord, tailWord_3368457, baseEnd_3368457] using wordTrace_append hprefix tailTrace_3368457
  have hstable : (prefixWord ++ tailWord_3368457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368457).length < 2 ^ (prefixWord ++ tailWord_3368457).sum := by decide
  have hdescent : baseEnd_3368457 < baseStart_3368457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368513 : List Nat := [1, 2, 5, 1, 1, 1, 1, 2, 3, 5]
def baseStart_3368513 : Nat := 118140960795 + 3368513 * 2 ^ 59
def prefixEnd_3368513 : Nat := 4983230072969 + 3 ^ 40 * 3368513 * 2
def baseEnd_3368513 : Nat := 1153110839945789607397331

theorem tailTrace_3368513 : CollatzResearch.WordTrace tailWord_3368513 prefixEnd_3368513 1153110839945789607397331 := by
  unfold tailWord_3368513
  simp only [CollatzResearch.WordTrace]
  refine ⟨122859762445460172063838193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81906508296973448042558795 122859762445460172063838193)
  ·
    refine ⟨92144821834095129047878645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122859762445460172063838193 92144821834095129047878645)
    ·
      refine ⟨8638577046946418348238623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92144821834095129047878645 8638577046946418348238623)
      ·
        refine ⟨12957865570419627522357935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8638577046946418348238623 12957865570419627522357935)
        ·
          refine ⟨19436798355629441283536903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12957865570419627522357935 19436798355629441283536903)
          ·
            refine ⟨29155197533444161925305355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19436798355629441283536903 29155197533444161925305355)
            ·
              refine ⟨43732796300166242887958033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29155197533444161925305355 43732796300166242887958033)
              ·
                refine ⟨32799597225124682165968525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43732796300166242887958033 32799597225124682165968525)
                ·
                  refine ⟨12299848959421755812238197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32799597225124682165968525 12299848959421755812238197)
                  ·
                    refine ⟨1153110839945789607397331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12299848959421755812238197 1153110839945789607397331)
                    ·
                      rfl

theorem cell22_3368513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_3368513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3368513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3368513 prefixEnd_3368513 := by exact prefixLift 3368513
  have htrace : WordTrace (prefixWord ++ tailWord_3368513) baseStart_3368513 baseEnd_3368513 := by
    simpa [prefixWord, tailWord_3368513, baseEnd_3368513] using wordTrace_append hprefix tailTrace_3368513
  have hstable : (prefixWord ++ tailWord_3368513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368513).length < 2 ^ (prefixWord ++ tailWord_3368513).sum := by decide
  have hdescent : baseEnd_3368513 < baseStart_3368513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368530 : List Nat := [3, 2, 2, 1, 2, 3, 2, 1, 1, 5]
def baseStart_3368530 : Nat := 118140960795 + 3368530 * 2 ^ 59
def prefixEnd_3368530 : Nat := 4983230072969 + 3 ^ 40 * 3368530 * 2
def baseEnd_3368530 : Nat := 1153116659393207229722279

theorem tailTrace_3368530 : CollatzResearch.WordTrace tailWord_3368530 prefixEnd_3368530 1153116659393207229722279 := by
  unfold tailWord_3368530
  simp only [CollatzResearch.WordTrace]
  refine ⟨30715095621599645991801761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81906921657599055978138029 30715095621599645991801761)
  ·
    refine ⟨23036321716199734493851321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30715095621599645991801761 23036321716199734493851321)
    ·
      refine ⟨17277241287149800870388491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23036321716199734493851321 17277241287149800870388491)
      ·
        refine ⟨25915861930724701305582737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17277241287149800870388491 25915861930724701305582737)
        ·
          refine ⟨19436896448043525979187053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25915861930724701305582737 19436896448043525979187053)
          ·
            refine ⟨7288836168016322242195145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19436896448043525979187053 7288836168016322242195145)
            ·
              refine ⟨5466627126012241681646359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7288836168016322242195145 5466627126012241681646359)
              ·
                refine ⟨8199940689018362522469539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5466627126012241681646359 8199940689018362522469539)
                ·
                  refine ⟨12299911033527543783704309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8199940689018362522469539 12299911033527543783704309)
                  ·
                    refine ⟨1153116659393207229722279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12299911033527543783704309 1153116659393207229722279)
                    ·
                      rfl

theorem cell22_3368530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_3368530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3368530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3368530 prefixEnd_3368530 := by exact prefixLift 3368530
  have htrace : WordTrace (prefixWord ++ tailWord_3368530) baseStart_3368530 baseEnd_3368530 := by
    simpa [prefixWord, tailWord_3368530, baseEnd_3368530] using wordTrace_append hprefix tailTrace_3368530
  have hstable : (prefixWord ++ tailWord_3368530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368530).length < 2 ^ (prefixWord ++ tailWord_3368530).sum := by decide
  have hdescent : baseEnd_3368530 < baseStart_3368530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368594 : List Nat := [3, 2, 3, 1, 4, 1, 2, 6]
def baseStart_3368594 : Nat := 118140960795 + 3368594 * 2 ^ 59
def prefixEnd_3368594 : Nat := 4983230072969 + 3 ^ 40 * 3368594 * 2
def baseEnd_3368594 : Nat := 128126507544570266235787

theorem tailTrace_3368594 : CollatzResearch.WordTrace tailWord_3368594 prefixEnd_3368594 128126507544570266235787 := by
  unfold tailWord_3368594
  simp only [CollatzResearch.WordTrace]
  refine ⟨30715679189541680724384209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81908477838777815265024557 30715679189541680724384209)
  ·
    refine ⟨23036759392156260543288157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30715679189541680724384209 23036759392156260543288157)
    ·
      refine ⟨8638784772058597703733059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23036759392156260543288157 8638784772058597703733059)
      ·
        refine ⟨12958177158087896555599589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8638784772058597703733059 12958177158087896555599589)
        ·
          refine ⟨2429658217141480604174923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12958177158087896555599589 2429658217141480604174923)
          ·
            refine ⟨3644487325712220906262385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2429658217141480604174923 3644487325712220906262385)
            ·
              refine ⟨2733365494284165679696789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3644487325712220906262385 2733365494284165679696789)
              ·
                refine ⟨128126507544570266235787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2733365494284165679696789 128126507544570266235787)
                ·
                  rfl

theorem cell22_3368594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 2, 6].length) (baseStart_3368594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3368594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3368594 prefixEnd_3368594 := by exact prefixLift 3368594
  have htrace : WordTrace (prefixWord ++ tailWord_3368594) baseStart_3368594 baseEnd_3368594 := by
    simpa [prefixWord, tailWord_3368594, baseEnd_3368594] using wordTrace_append hprefix tailTrace_3368594
  have hstable : (prefixWord ++ tailWord_3368594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368594).length < 2 ^ (prefixWord ++ tailWord_3368594).sum := by decide
  have hdescent : baseEnd_3368594 < baseStart_3368594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368609 : List Nat := [1, 2, 3, 3, 2, 1, 3, 3, 1, 3]
def baseStart_3368609 : Nat := 118140960795 + 3368609 * 2 ^ 59
def prefixEnd_3368609 : Nat := 4983230072969 + 3 ^ 40 * 3368609 * 2
def baseEnd_3368609 : Nat := 1153143702707677356997037

theorem tailTrace_3368609 : CollatzResearch.WordTrace tailWord_3368609 prefixEnd_3368609 1153143702707677356997037 := by
  unfold tailWord_3368609
  simp only [CollatzResearch.WordTrace]
  refine ⟨122863263853112380459332881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81908842568741586972888587 122863263853112380459332881)
  ·
    refine ⟨92147447889834285344499661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122863263853112380459332881 92147447889834285344499661)
    ·
      refine ⟨34555292958687857004187373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92147447889834285344499661 34555292958687857004187373)
      ·
        refine ⟨12958234859507946376570265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34555292958687857004187373 12958234859507946376570265)
        ·
          refine ⟨9718676144630959782427699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12958234859507946376570265 9718676144630959782427699)
          ·
            refine ⟨14578014216946439673641549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9718676144630959782427699 14578014216946439673641549)
            ·
              refine ⟨5466755331354914877615581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14578014216946439673641549 5466755331354914877615581)
              ·
                refine ⟨2050033249258093079105843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5466755331354914877615581 2050033249258093079105843)
                ·
                  refine ⟨3075049873887139618658765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2050033249258093079105843 3075049873887139618658765)
                  ·
                    refine ⟨1153143702707677356997037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3075049873887139618658765 1153143702707677356997037)
                    ·
                      rfl

theorem cell22_3368609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 3, 1, 3].length) (baseStart_3368609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3368609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3368609 prefixEnd_3368609 := by exact prefixLift 3368609
  have htrace : WordTrace (prefixWord ++ tailWord_3368609) baseStart_3368609 baseEnd_3368609 := by
    simpa [prefixWord, tailWord_3368609, baseEnd_3368609] using wordTrace_append hprefix tailTrace_3368609
  have hstable : (prefixWord ++ tailWord_3368609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368609).length < 2 ^ (prefixWord ++ tailWord_3368609).sum := by decide
  have hdescent : baseEnd_3368609 < baseStart_3368609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368652 : List Nat := [2, 2, 1, 5, 2, 1, 1, 1, 3, 4]
def baseStart_3368652 : Nat := 118140960795 + 3368652 * 2 ^ 59
def prefixEnd_3368652 : Nat := 4983230072969 + 3 ^ 40 * 3368652 * 2
def baseEnd_3368652 : Nat := 1153158422486439578171905

theorem tailTrace_3368652 : CollatzResearch.WordTrace tailWord_3368652 prefixEnd_3368652 1153158422486439578171905 := by
  unfold tailWord_3368652
  simp only [CollatzResearch.WordTrace]
  refine ⟨61432416095978299401574105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81909888127971065868765473 61432416095978299401574105)
  ·
    refine ⟨46074312071983724551180579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61432416095978299401574105 46074312071983724551180579)
    ·
      refine ⟨69111468107975586826770869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46074312071983724551180579 69111468107975586826770869)
      ·
        refine ⟨6479200135122711265009769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69111468107975586826770869 6479200135122711265009769)
        ·
          refine ⟨4859400101342033448757327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6479200135122711265009769 4859400101342033448757327)
          ·
            refine ⟨7289100152013050173135991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4859400101342033448757327 7289100152013050173135991)
            ·
              refine ⟨10933650228019575259703987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7289100152013050173135991 10933650228019575259703987)
              ·
                refine ⟨16400475342029362889555981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10933650228019575259703987 16400475342029362889555981)
                ·
                  refine ⟨6150178253261011083583493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16400475342029362889555981 6150178253261011083583493)
                  ·
                    refine ⟨1153158422486439578171905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6150178253261011083583493 1153158422486439578171905)
                    ·
                      rfl

theorem cell22_3368652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 3, 4].length) (baseStart_3368652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3368652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3368652 prefixEnd_3368652 := by exact prefixLift 3368652
  have htrace : WordTrace (prefixWord ++ tailWord_3368652) baseStart_3368652 baseEnd_3368652 := by
    simpa [prefixWord, tailWord_3368652, baseEnd_3368652] using wordTrace_append hprefix tailTrace_3368652
  have hstable : (prefixWord ++ tailWord_3368652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368652).length < 2 ^ (prefixWord ++ tailWord_3368652).sum := by decide
  have hdescent : baseEnd_3368652 < baseStart_3368652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368665 : List Nat := [1, 2, 1, 2, 3, 4, 1, 2, 1, 5]
def baseStart_3368665 : Nat := 118140960795 + 3368665 * 2 ^ 59
def prefixEnd_3368665 : Nat := 4983230072969 + 3 ^ 40 * 3368665 * 2
def baseEnd_3368665 : Nat := 1153162872652111877596865

theorem tailTrace_3368665 : CollatzResearch.WordTrace tailWord_3368665 prefixEnd_3368665 1153162872652111877596865 := by
  unfold tailWord_3368665
  simp only [CollatzResearch.WordTrace]
  refine ⟨122865306340909502023371449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81910204227273001348914299 122865306340909502023371449)
  ·
    refine ⟨92148979755682126517528587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122865306340909502023371449 92148979755682126517528587)
    ·
      refine ⟨138223469633523189776292881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92148979755682126517528587 138223469633523189776292881)
      ·
        refine ⟨103667602225142392332219661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138223469633523189776292881 103667602225142392332219661)
        ·
          refine ⟨38875350834428397124582373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103667602225142392332219661 38875350834428397124582373)
          ·
            refine ⟨7289128281455324460859195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38875350834428397124582373 7289128281455324460859195)
            ·
              refine ⟨10933692422182986691288793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7289128281455324460859195 10933692422182986691288793)
              ·
                refine ⟨8200269316637240018466595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10933692422182986691288793 8200269316637240018466595)
                ·
                  refine ⟨12300403974955860027699893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8200269316637240018466595 12300403974955860027699893)
                  ·
                    refine ⟨1153162872652111877596865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12300403974955860027699893 1153162872652111877596865)
                    ·
                      rfl

theorem cell22_3368665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 2, 1, 5].length) (baseStart_3368665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3368665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3368665 prefixEnd_3368665 := by exact prefixLift 3368665
  have htrace : WordTrace (prefixWord ++ tailWord_3368665) baseStart_3368665 baseEnd_3368665 := by
    simpa [prefixWord, tailWord_3368665, baseEnd_3368665] using wordTrace_append hprefix tailTrace_3368665
  have hstable : (prefixWord ++ tailWord_3368665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368665).length < 2 ^ (prefixWord ++ tailWord_3368665).sum := by decide
  have hdescent : baseEnd_3368665 < baseStart_3368665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368682 : List Nat := [3, 1, 3, 1, 1, 1, 3, 4, 2, 3]
def baseStart_3368682 : Nat := 118140960795 + 3368682 * 2 ^ 59
def prefixEnd_3368682 : Nat := 4983230072969 + 3 ^ 40 * 3368682 * 2
def baseEnd_3368682 : Nat := 1153168692099529499921813

theorem tailTrace_3368682 : CollatzResearch.WordTrace tailWord_3368682 prefixEnd_3368682 1153168692099529499921813 := by
  unfold tailWord_3368682
  simp only [CollatzResearch.WordTrace]
  refine ⟨30716481595461978481685075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81910617587898609284493533 30716481595461978481685075)
  ·
    refine ⟨46074722393192967722527613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30716481595461978481685075 46074722393192967722527613)
    ·
      refine ⟨17278020897447362895947855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46074722393192967722527613 17278020897447362895947855)
      ·
        refine ⟨25917031346171044343921783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17278020897447362895947855 25917031346171044343921783)
        ·
          refine ⟨38875547019256566515882675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25917031346171044343921783 38875547019256566515882675)
          ·
            refine ⟨58313320528884849773824013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38875547019256566515882675 58313320528884849773824013)
            ·
              refine ⟨21867495198331818665184005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58313320528884849773824013 21867495198331818665184005)
              ·
                refine ⟨4100155349687215999722001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21867495198331818665184005 4100155349687215999722001)
                ·
                  refine ⟨3075116512265411999791501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4100155349687215999722001 3075116512265411999791501)
                  ·
                    refine ⟨1153168692099529499921813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3075116512265411999791501 1153168692099529499921813)
                    ·
                      rfl

theorem cell22_3368682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_3368682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3368682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3368682 prefixEnd_3368682 := by exact prefixLift 3368682
  have htrace : WordTrace (prefixWord ++ tailWord_3368682) baseStart_3368682 baseEnd_3368682 := by
    simpa [prefixWord, tailWord_3368682, baseEnd_3368682] using wordTrace_append hprefix tailTrace_3368682
  have hstable : (prefixWord ++ tailWord_3368682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368682).length < 2 ^ (prefixWord ++ tailWord_3368682).sum := by decide
  have hdescent : baseEnd_3368682 < baseStart_3368682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368744 : List Nat := [2, 1, 5, 1, 1, 3, 2, 1, 3, 3]
def baseStart_3368744 : Nat := 118140960795 + 3368744 * 2 ^ 59
def prefixEnd_3368744 : Nat := 4983230072969 + 3 ^ 40 * 3368744 * 2
def baseEnd_3368744 : Nat := 1153189915966582004871623

theorem tailTrace_3368744 : CollatzResearch.WordTrace tailWord_3368744 prefixEnd_3368744 1153189915966582004871623 := by
  unfold tailWord_3368744
  simp only [CollatzResearch.WordTrace]
  refine ⟨61434093853811649257748643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81912125138415532343664857 61434093853811649257748643)
  ·
    refine ⟨92151140780717473886622965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61434093853811649257748643 92151140780717473886622965)
    ·
      refine ⟨8639169448192263176870903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92151140780717473886622965 8639169448192263176870903)
      ·
        refine ⟨12958754172288394765306355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8639169448192263176870903 12958754172288394765306355)
        ·
          refine ⟨19438131258432592147959533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12958754172288394765306355 19438131258432592147959533)
          ·
            refine ⟨7289299221912222055484825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19438131258432592147959533 7289299221912222055484825)
            ·
              refine ⟨5466974416434166541613619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7289299221912222055484825 5466974416434166541613619)
              ·
                refine ⟨8200461624651249812420429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5466974416434166541613619 8200461624651249812420429)
                ·
                  refine ⟨3075173109244218679657661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8200461624651249812420429 3075173109244218679657661)
                  ·
                    refine ⟨1153189915966582004871623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3075173109244218679657661 1153189915966582004871623)
                    ·
                      rfl

theorem cell22_3368744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_3368744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3368744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3368744 prefixEnd_3368744 := by exact prefixLift 3368744
  have htrace : WordTrace (prefixWord ++ tailWord_3368744) baseStart_3368744 baseEnd_3368744 := by
    simpa [prefixWord, tailWord_3368744, baseEnd_3368744] using wordTrace_append hprefix tailTrace_3368744
  have hstable : (prefixWord ++ tailWord_3368744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368744).length < 2 ^ (prefixWord ++ tailWord_3368744).sum := by decide
  have hdescent : baseEnd_3368744 < baseStart_3368744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368774 : List Nat := [6, 1, 1, 2, 1, 1, 1, 2, 7]
def baseStart_3368774 : Nat := 118140960795 + 3368774 * 2 ^ 59
def prefixEnd_3368774 : Nat := 4983230072969 + 3 ^ 40 * 3368774 * 2
def baseEnd_3368774 : Nat := 384400061859890642207177

theorem tailTrace_3368774 : CollatzResearch.WordTrace tailWord_3368774 prefixEnd_3368774 384400061859890642207177 := by
  unfold tailWord_3368774
  simp only [CollatzResearch.WordTrace]
  refine ⟨3839665059297331676221543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 81912854598343075759392917 3839665059297331676221543)
  ·
    refine ⟨5759497588945997514332315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3839665059297331676221543 5759497588945997514332315)
    ·
      refine ⟨8639246383418996271498473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5759497588945997514332315 8639246383418996271498473)
      ·
        refine ⟨6479434787564247203623855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8639246383418996271498473 6479434787564247203623855)
        ·
          refine ⟨9719152181346370805435783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6479434787564247203623855 9719152181346370805435783)
          ·
            refine ⟨14578728272019556208153675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9719152181346370805435783 14578728272019556208153675)
            ·
              refine ⟨21868092408029334312230513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14578728272019556208153675 21868092408029334312230513)
              ·
                refine ⟨16401069306022000734172885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21868092408029334312230513 16401069306022000734172885)
                ·
                  refine ⟨384400061859890642207177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16401069306022000734172885 384400061859890642207177)
                  ·
                    rfl

theorem cell22_3368774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_3368774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3368774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3368774 prefixEnd_3368774 := by exact prefixLift 3368774
  have htrace : WordTrace (prefixWord ++ tailWord_3368774) baseStart_3368774 baseEnd_3368774 := by
    simpa [prefixWord, tailWord_3368774, baseEnd_3368774] using wordTrace_append hprefix tailTrace_3368774
  have hstable : (prefixWord ++ tailWord_3368774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368774).length < 2 ^ (prefixWord ++ tailWord_3368774).sum := by decide
  have hdescent : baseEnd_3368774 < baseStart_3368774 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368832 : List Nat := [2, 1, 1, 2, 1, 2, 6, 1, 2, 4]
def baseStart_3368832 : Nat := 118140960795 + 3368832 * 2 ^ 59
def prefixEnd_3368832 : Nat := 4983230072969 + 3 ^ 40 * 3368832 * 2
def baseEnd_3368832 : Nat := 1153220040164979108671353

theorem tailTrace_3368832 : CollatzResearch.WordTrace tailWord_3368832 prefixEnd_3368832 1153220040164979108671353 := by
  unfold tailWord_3368832
  simp only [CollatzResearch.WordTrace]
  refine ⟨61435698665652244772350375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81914264887536326363133833 61435698665652244772350375)
  ·
    refine ⟨92153547998478367158525563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61435698665652244772350375 92153547998478367158525563)
    ·
      refine ⟨138230321997717550737788345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92153547998478367158525563 138230321997717550737788345)
      ·
        refine ⟨103672741498288163053341259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138230321997717550737788345 103672741498288163053341259)
        ·
          refine ⟨155509112247432244580011889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103672741498288163053341259 155509112247432244580011889)
          ·
            refine ⟨116631834185574183435008917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155509112247432244580011889 116631834185574183435008917)
            ·
              refine ⟨5467117227448789848516043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 116631834185574183435008917 5467117227448789848516043)
              ·
                refine ⟨8200675841173184772774065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5467117227448789848516043 8200675841173184772774065)
                ·
                  refine ⟨6150506880879888579580549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8200675841173184772774065 6150506880879888579580549)
                  ·
                    refine ⟨1153220040164979108671353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6150506880879888579580549 1153220040164979108671353)
                    ·
                      rfl

theorem cell22_3368832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 1, 2, 4].length) (baseStart_3368832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3368832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3368832 prefixEnd_3368832 := by exact prefixLift 3368832
  have htrace : WordTrace (prefixWord ++ tailWord_3368832) baseStart_3368832 baseEnd_3368832 := by
    simpa [prefixWord, tailWord_3368832, baseEnd_3368832] using wordTrace_append hprefix tailTrace_3368832
  have hstable : (prefixWord ++ tailWord_3368832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368832).length < 2 ^ (prefixWord ++ tailWord_3368832).sum := by decide
  have hdescent : baseEnd_3368832 < baseStart_3368832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368896 : List Nat := [2, 1, 1, 2, 3, 2, 4, 3, 1, 3]
def baseStart_3368896 : Nat := 118140960795 + 3368896 * 2 ^ 59
def prefixEnd_3368896 : Nat := 4983230072969 + 3 ^ 40 * 3368896 * 2
def baseEnd_3368896 : Nat := 1153241948672904275071157

theorem tailTrace_3368896 : CollatzResearch.WordTrace tailWord_3368896 prefixEnd_3368896 1153241948672904275071157 := by
  unfold tailWord_3368896
  simp only [CollatzResearch.WordTrace]
  refine ⟨61436865801536314237515271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81915821068715085650020361 61436865801536314237515271)
  ·
    refine ⟨92155298702304471356272907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61436865801536314237515271 92155298702304471356272907)
    ·
      refine ⟨138232948053456707034409361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92155298702304471356272907 138232948053456707034409361)
      ·
        refine ⟨103674711040092530275807021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138232948053456707034409361 103674711040092530275807021)
        ·
          refine ⟨38878016640034698853427633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103674711040092530275807021 38878016640034698853427633)
          ·
            refine ⟨29158512480026024140070725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38878016640034698853427633 29158512480026024140070725)
            ·
              refine ⟨5467221090004879526263261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29158512480026024140070725 5467221090004879526263261)
              ·
                refine ⟨2050207908751829822348723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5467221090004879526263261 2050207908751829822348723)
                ·
                  refine ⟨3075311863127744733523085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2050207908751829822348723 3075311863127744733523085)
                  ·
                    refine ⟨1153241948672904275071157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3075311863127744733523085 1153241948672904275071157)
                    ·
                      rfl

theorem cell22_3368896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 3, 1, 3].length) (baseStart_3368896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3368896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3368896 prefixEnd_3368896 := by exact prefixLift 3368896
  have htrace : WordTrace (prefixWord ++ tailWord_3368896) baseStart_3368896 baseEnd_3368896 := by
    simpa [prefixWord, tailWord_3368896, baseEnd_3368896] using wordTrace_append hprefix tailTrace_3368896
  have hstable : (prefixWord ++ tailWord_3368896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368896).length < 2 ^ (prefixWord ++ tailWord_3368896).sum := by decide
  have hdescent : baseEnd_3368896 < baseStart_3368896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368952 : List Nat := [2, 1, 2, 1, 1, 3, 2, 4, 1, 5]
def baseStart_3368952 : Nat := 118140960795 + 3368952 * 2 ^ 59
def prefixEnd_3368952 : Nat := 4983230072969 + 3 ^ 40 * 3368952 * 2
def baseEnd_3368952 : Nat := 1153261118617338795670985

theorem tailTrace_3368952 : CollatzResearch.WordTrace tailWord_3368952 prefixEnd_3368952 1153261118617338795670985 := by
  unfold tailWord_3368952
  simp only [CollatzResearch.WordTrace]
  refine ⟨61437887045434875019534555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81917182727246500026046073 61437887045434875019534555)
  ·
    refine ⟨92156830568152312529301833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61437887045434875019534555 92156830568152312529301833)
    ·
      refine ⟨69117622926114234396976375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92156830568152312529301833 69117622926114234396976375)
      ·
        refine ⟨103676434389171351595464563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69117622926114234396976375 103676434389171351595464563)
        ·
          refine ⟨155514651583757027393196845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103676434389171351595464563 155514651583757027393196845)
          ·
            refine ⟨58317994343908885272448817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155514651583757027393196845 58317994343908885272448817)
            ·
              refine ⟨43738495757931663954336613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58317994343908885272448817 43738495757931663954336613)
              ·
                refine ⟨8200967954612186991438115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43738495757931663954336613 8200967954612186991438115)
                ·
                  refine ⟨12301451931918280487157173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8200967954612186991438115 12301451931918280487157173)
                  ·
                    refine ⟨1153261118617338795670985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12301451931918280487157173 1153261118617338795670985)
                    ·
                      rfl

theorem cell22_3368952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4, 1, 5].length) (baseStart_3368952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3368952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3368952 prefixEnd_3368952 := by exact prefixLift 3368952
  have htrace : WordTrace (prefixWord ++ tailWord_3368952) baseStart_3368952 baseEnd_3368952 := by
    simpa [prefixWord, tailWord_3368952, baseEnd_3368952] using wordTrace_append hprefix tailTrace_3368952
  have hstable : (prefixWord ++ tailWord_3368952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368952).length < 2 ^ (prefixWord ++ tailWord_3368952).sum := by decide
  have hdescent : baseEnd_3368952 < baseStart_3368952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368971 : List Nat := [1, 1, 1, 1, 6, 1, 5, 2, 4]
def baseStart_3368971 : Nat := 118140960795 + 3368971 * 2 ^ 59
def prefixEnd_3368971 : Nat := 4983230072969 + 3 ^ 40 * 3368971 * 2
def baseEnd_3368971 : Nat := 384422540901876359815309

theorem tailTrace_3368971 : CollatzResearch.WordTrace tailWord_3368971 prefixEnd_3368971 384422540901876359815309 := by
  unfold tailWord_3368971
  simp only [CollatzResearch.WordTrace]
  refine ⟨122876467077800916284010767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81917644718533944189340511 122876467077800916284010767)
  ·
    refine ⟨184314700616701374426016151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122876467077800916284010767 184314700616701374426016151)
    ·
      refine ⟨276472050925052061639024227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184314700616701374426016151 276472050925052061639024227)
      ·
        refine ⟨414708076387578092458536341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276472050925052061639024227 414708076387578092458536341)
        ·
          refine ⟨19439441080667723083993891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 414708076387578092458536341 19439441080667723083993891)
          ·
            refine ⟨29159161621001584625990837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19439441080667723083993891 29159161621001584625990837)
            ·
              refine ⟨2733671401968898558686641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29159161621001584625990837 2733671401968898558686641)
              ·
                refine ⟨2050253551476673919014981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2733671401968898558686641 2050253551476673919014981)
                ·
                  refine ⟨384422540901876359815309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2050253551476673919014981 384422540901876359815309)
                  ·
                    rfl

theorem cell22_3368971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5, 2, 4].length) (baseStart_3368971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3368971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3368971 prefixEnd_3368971 := by exact prefixLift 3368971
  have htrace : WordTrace (prefixWord ++ tailWord_3368971) baseStart_3368971 baseEnd_3368971 := by
    simpa [prefixWord, tailWord_3368971, baseEnd_3368971] using wordTrace_append hprefix tailTrace_3368971
  have hstable : (prefixWord ++ tailWord_3368971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368971).length < 2 ^ (prefixWord ++ tailWord_3368971).sum := by decide
  have hdescent : baseEnd_3368971 < baseStart_3368971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368986 : List Nat := [3, 1, 1, 3, 1, 4, 1, 3, 2, 3]
def baseStart_3368986 : Nat := 118140960795 + 3368986 * 2 ^ 59
def prefixEnd_3368986 : Nat := 4983230072969 + 3 ^ 40 * 3368986 * 2
def baseEnd_3368986 : Nat := 1153272757512174040320881

theorem tailTrace_3368986 : CollatzResearch.WordTrace tailWord_3368986 prefixEnd_3368986 1153272757512174040320881 := by
  unfold tailWord_3368986
  simp only [CollatzResearch.WordTrace]
  refine ⟨30719253543186643461451703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81918009448497715897204541 30719253543186643461451703)
  ·
    refine ⟨46078880314779965192177555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30719253543186643461451703 46078880314779965192177555)
    ·
      refine ⟨69118320472169947788266333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46078880314779965192177555 69118320472169947788266333)
      ·
        refine ⟨25919370177063730420599875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69118320472169947788266333 25919370177063730420599875)
        ·
          refine ⟨38879055265595595630899813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25919370177063730420599875 38879055265595595630899813)
          ·
            refine ⟨7289822862299174180793715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38879055265595595630899813 7289822862299174180793715)
            ·
              refine ⟨10934734293448761271190573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7289822862299174180793715 10934734293448761271190573)
              ·
                refine ⟨4100525360043285476696465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10934734293448761271190573 4100525360043285476696465)
                ·
                  refine ⟨3075394020032464107522349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4100525360043285476696465 3075394020032464107522349)
                  ·
                    refine ⟨1153272757512174040320881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3075394020032464107522349 1153272757512174040320881)
                    ·
                      rfl

theorem cell22_3368986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 3, 2, 3].length) (baseStart_3368986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3368986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3368986 prefixEnd_3368986 := by exact prefixLift 3368986
  have htrace : WordTrace (prefixWord ++ tailWord_3368986) baseStart_3368986 baseEnd_3368986 := by
    simpa [prefixWord, tailWord_3368986, baseEnd_3368986] using wordTrace_append hprefix tailTrace_3368986
  have hstable : (prefixWord ++ tailWord_3368986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368986).length < 2 ^ (prefixWord ++ tailWord_3368986).sum := by decide
  have hdescent : baseEnd_3368986 < baseStart_3368986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369022 : List Nat := [4, 2, 1, 3, 3, 1, 2, 2, 4]
def baseStart_3369022 : Nat := 118140960795 + 3369022 * 2 ^ 59
def prefixEnd_3369022 : Nat := 4983230072969 + 3 ^ 40 * 3369022 * 2
def baseEnd_3369022 : Nat := 384428360349293982140257

theorem tailTrace_3369022 : CollatzResearch.WordTrace tailWord_3369022 prefixEnd_3369022 384428360349293982140257 := by
  unfold tailWord_3369022
  simp only [CollatzResearch.WordTrace]
  refine ⟨15359790900077018999264665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81918884800410767996078213 15359790900077018999264665)
  ·
    refine ⟨11519843175057764249448499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15359790900077018999264665 11519843175057764249448499)
    ·
      refine ⟨17279764762586646374172749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11519843175057764249448499 17279764762586646374172749)
      ·
        refine ⟨6479911785969992390314781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17279764762586646374172749 6479911785969992390314781)
        ·
          refine ⟨2429966919738747146368043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6479911785969992390314781 2429966919738747146368043)
          ·
            refine ⟨3644950379608120719552065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2429966919738747146368043 3644950379608120719552065)
            ·
              refine ⟨2733712784706090539664049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3644950379608120719552065 2733712784706090539664049)
              ·
                refine ⟨2050284588529567904748037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2733712784706090539664049 2050284588529567904748037)
                ·
                  refine ⟨384428360349293982140257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2050284588529567904748037 384428360349293982140257)
                  ·
                    rfl

theorem cell22_3369022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_3369022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3369022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3369022 prefixEnd_3369022 := by exact prefixLift 3369022
  have htrace : WordTrace (prefixWord ++ tailWord_3369022) baseStart_3369022 baseEnd_3369022 := by
    simpa [prefixWord, tailWord_3369022, baseEnd_3369022] using wordTrace_append hprefix tailTrace_3369022
  have hstable : (prefixWord ++ tailWord_3369022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369022).length < 2 ^ (prefixWord ++ tailWord_3369022).sum := by decide
  have hdescent : baseEnd_3369022 < baseStart_3369022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369078 : List Nat := [5, 1, 1, 2, 1, 4, 1, 2, 5]
def baseStart_3369078 : Nat := 118140960795 + 3369078 * 2 ^ 59
def prefixEnd_3369078 : Nat := 4983230072969 + 3 ^ 40 * 3369078 * 2
def baseEnd_3369078 : Nat := 384434750330772155673533

theorem tailTrace_3369078 : CollatzResearch.WordTrace tailWord_3369078 prefixEnd_3369078 384434750330772155673533 := by
  unfold tailWord_3369078
  simp only [CollatzResearch.WordTrace]
  refine ⟨7680023105525829597384743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81920246458942182372103925 7680023105525829597384743)
  ·
    refine ⟨11520034658288744396077115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7680023105525829597384743 11520034658288744396077115)
    ·
      refine ⟨17280051987433116594115673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11520034658288744396077115 17280051987433116594115673)
      ·
        refine ⟨12960038990574837445586755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17280051987433116594115673 12960038990574837445586755)
        ·
          refine ⟨19440058485862256168380133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12960038990574837445586755 19440058485862256168380133)
          ·
            refine ⟨3645010966099173031571275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19440058485862256168380133 3645010966099173031571275)
            ·
              refine ⟨5467516449148759547356913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3645010966099173031571275 5467516449148759547356913)
              ·
                refine ⟨4100637336861569660517685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5467516449148759547356913 4100637336861569660517685)
                ·
                  refine ⟨384434750330772155673533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4100637336861569660517685 384434750330772155673533)
                  ·
                    rfl

theorem cell22_3369078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_3369078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3369078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3369078 prefixEnd_3369078 := by exact prefixLift 3369078
  have htrace : WordTrace (prefixWord ++ tailWord_3369078) baseStart_3369078 baseEnd_3369078 := by
    simpa [prefixWord, tailWord_3369078, baseEnd_3369078] using wordTrace_append hprefix tailTrace_3369078
  have hstable : (prefixWord ++ tailWord_3369078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369078).length < 2 ^ (prefixWord ++ tailWord_3369078).sum := by decide
  have hdescent : baseEnd_3369078 < baseStart_3369078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369087 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 1, 11]
def baseStart_3369087 : Nat := 118140960795 + 3369087 * 2 ^ 59
def prefixEnd_3369087 : Nat := 4983230072969 + 3 ^ 40 * 3369087 * 2
def baseEnd_3369087 : Nat := 1153307331876243443545571

theorem tailTrace_3369087 : CollatzResearch.WordTrace tailWord_3369087 prefixEnd_3369087 1153307331876243443545571 := by
  unfold tailWord_3369087
  simp only [CollatzResearch.WordTrace]
  refine ⟨122880697945380668095233515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81920465296920445396822343 122880697945380668095233515)
  ·
    refine ⟨184321046918071002142850273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122880697945380668095233515 184321046918071002142850273)
    ·
      refine ⟨138240785188553251607137705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184321046918071002142850273 138240785188553251607137705)
      ·
        refine ⟨103680588891414938705353279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138240785188553251607137705 103680588891414938705353279)
        ·
          refine ⟨155520883337122408058029919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103680588891414938705353279 155520883337122408058029919)
          ·
            refine ⟨233281325005683612087044879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155520883337122408058029919 233281325005683612087044879)
            ·
              refine ⟨349921987508525418130567319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233281325005683612087044879 349921987508525418130567319)
              ·
                refine ⟨524882981262788127195850979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 349921987508525418130567319 524882981262788127195850979)
                ·
                  refine ⟨787324471894182190793776469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 524882981262788127195850979 787324471894182190793776469)
                  ·
                    refine ⟨1153307331876243443545571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 787324471894182190793776469 1153307331876243443545571)
                    ·
                      rfl

theorem cell22_3369087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 11].length) (baseStart_3369087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3369087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3369087 prefixEnd_3369087 := by exact prefixLift 3369087
  have htrace : WordTrace (prefixWord ++ tailWord_3369087) baseStart_3369087 baseEnd_3369087 := by
    simpa [prefixWord, tailWord_3369087, baseEnd_3369087] using wordTrace_append hprefix tailTrace_3369087
  have hstable : (prefixWord ++ tailWord_3369087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369087).length < 2 ^ (prefixWord ++ tailWord_3369087).sum := by decide
  have hdescent : baseEnd_3369087 < baseStart_3369087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369121 : List Nat := [1, 2, 3, 3, 1, 2, 1, 2, 4, 3]
def baseStart_3369121 : Nat := 118140960795 + 3369121 * 2 ^ 59
def prefixEnd_3369121 : Nat := 4983230072969 + 3 ^ 40 * 3369121 * 2
def baseEnd_3369121 : Nat := 1153318970771078688195467

theorem tailTrace_3369121 : CollatzResearch.WordTrace tailWord_3369121 prefixEnd_3369121 1153318970771078688195467 := by
  unfold tailWord_3369121
  simp only [CollatzResearch.WordTrace]
  refine ⟨122881938027257491901971217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81921292018171661267980811 122881938027257491901971217)
  ·
    refine ⟨92161453520443118926478413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122881938027257491901971217 92161453520443118926478413)
    ·
      refine ⟨34560545070166169597429405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92161453520443118926478413 34560545070166169597429405)
      ·
        refine ⟨12960204401312313599036027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34560545070166169597429405 12960204401312313599036027)
        ·
          refine ⟨19440306601968470398554041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12960204401312313599036027 19440306601968470398554041)
          ·
            refine ⟨14580229951476352798915531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19440306601968470398554041 14580229951476352798915531)
            ·
              refine ⟨21870344927214529198373297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14580229951476352798915531 21870344927214529198373297)
              ·
                refine ⟨16402758695410896898779973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21870344927214529198373297 16402758695410896898779973)
                ·
                  refine ⟨3075517255389543168521245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16402758695410896898779973 3075517255389543168521245)
                  ·
                    refine ⟨1153318970771078688195467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3075517255389543168521245 1153318970771078688195467)
                    ·
                      rfl

theorem cell22_3369121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 4, 3].length) (baseStart_3369121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3369121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3369121 prefixEnd_3369121 := by exact prefixLift 3369121
  have htrace : WordTrace (prefixWord ++ tailWord_3369121) baseStart_3369121 baseEnd_3369121 := by
    simpa [prefixWord, tailWord_3369121, baseEnd_3369121] using wordTrace_append hprefix tailTrace_3369121
  have hstable : (prefixWord ++ tailWord_3369121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369121).length < 2 ^ (prefixWord ++ tailWord_3369121).sum := by decide
  have hdescent : baseEnd_3369121 < baseStart_3369121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369183 : List Nat := [1, 1, 2, 3, 2, 1, 1, 7, 1, 3]
def baseStart_3369183 : Nat := 118140960795 + 3369183 * 2 ^ 59
def prefixEnd_3369183 : Nat := 4983230072969 + 3 ^ 40 * 3369183 * 2
def baseEnd_3369183 : Nat := 1153340194638131193145277

theorem tailTrace_3369183 : CollatzResearch.WordTrace tailWord_3369183 prefixEnd_3369183 1153340194638131193145277 := by
  unfold tailWord_3369183
  simp only [CollatzResearch.WordTrace]
  refine ⟨122884199353032876490728203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81922799568688584327152135 122884199353032876490728203)
  ·
    refine ⟨184326299029549314736092305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122884199353032876490728203 184326299029549314736092305)
    ·
      refine ⟨138244724272161986052069229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184326299029549314736092305 138244724272161986052069229)
      ·
        refine ⟨51841771602060744769525961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138244724272161986052069229 51841771602060744769525961)
        ·
          refine ⟨38881328701545558577144471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51841771602060744769525961 38881328701545558577144471)
          ·
            refine ⟨58321993052318337865716707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38881328701545558577144471 58321993052318337865716707)
            ·
              refine ⟨87482989578477506798575061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58321993052318337865716707 87482989578477506798575061)
              ·
                refine ⟨2050382568245566565591603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 87482989578477506798575061 2050382568245566565591603)
                ·
                  refine ⟨3075573852368349848387405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2050382568245566565591603 3075573852368349848387405)
                  ·
                    refine ⟨1153340194638131193145277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3075573852368349848387405 1153340194638131193145277)
                    ·
                      rfl

theorem cell22_3369183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 7, 1, 3].length) (baseStart_3369183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3369183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3369183 prefixEnd_3369183 := by exact prefixLift 3369183
  have htrace : WordTrace (prefixWord ++ tailWord_3369183) baseStart_3369183 baseEnd_3369183 := by
    simpa [prefixWord, tailWord_3369183, baseEnd_3369183] using wordTrace_append hprefix tailTrace_3369183
  have hstable : (prefixWord ++ tailWord_3369183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369183).length < 2 ^ (prefixWord ++ tailWord_3369183).sum := by decide
  have hdescent : baseEnd_3369183 < baseStart_3369183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369196 : List Nat := [2, 2, 1, 1, 2, 3, 4, 2, 5]
def baseStart_3369196 : Nat := 118140960795 + 3369196 * 2 ^ 59
def prefixEnd_3369196 : Nat := 4983230072969 + 3 ^ 40 * 3369196 * 2
def baseEnd_3369196 : Nat := 384448214934601164190079

theorem tailTrace_3369196 : CollatzResearch.WordTrace tailWord_3369196 prefixEnd_3369196 384448214934601164190079 := by
  unfold tailWord_3369196
  simp only [CollatzResearch.WordTrace]
  refine ⟨61442336750992889855475721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81923115667990519807300961 61442336750992889855475721)
  ·
    refine ⟨46081752563244667391606791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61442336750992889855475721 46081752563244667391606791)
    ·
      refine ⟨69122628844867001087410187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46081752563244667391606791 69122628844867001087410187)
      ·
        refine ⟨103683943267300501631115281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69122628844867001087410187 103683943267300501631115281)
        ·
          refine ⟨77762957450475376223336461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103683943267300501631115281 77762957450475376223336461)
          ·
            refine ⟨29161109043928266083751173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77762957450475376223336461 29161109043928266083751173)
            ·
              refine ⟨5467707945736549890703345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29161109043928266083751173 5467707945736549890703345)
              ·
                refine ⟨4100780959302412418027509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5467707945736549890703345 4100780959302412418027509)
                ·
                  refine ⟨384448214934601164190079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4100780959302412418027509 384448214934601164190079)
                  ·
                    rfl

theorem cell22_3369196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 5].length) (baseStart_3369196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3369196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3369196 prefixEnd_3369196 := by exact prefixLift 3369196
  have htrace : WordTrace (prefixWord ++ tailWord_3369196) baseStart_3369196 baseEnd_3369196 := by
    simpa [prefixWord, tailWord_3369196, baseEnd_3369196] using wordTrace_append hprefix tailTrace_3369196
  have hstable : (prefixWord ++ tailWord_3369196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369196).length < 2 ^ (prefixWord ++ tailWord_3369196).sum := by decide
  have hdescent : baseEnd_3369196 < baseStart_3369196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369226 : List Nat := [3, 1, 2, 2, 1, 1, 4, 1, 3, 4]
def baseStart_3369226 : Nat := 118140960795 + 3369226 * 2 ^ 59
def prefixEnd_3369226 : Nat := 4983230072969 + 3 ^ 40 * 3369226 * 2
def baseEnd_3369226 : Nat := 1153354914416893414320145

theorem tailTrace_3369226 : CollatzResearch.WordTrace tailWord_3369226 prefixEnd_3369226 1153354914416893414320145 := by
  unfold tailWord_3369226
  simp only [CollatzResearch.WordTrace]
  refine ⟨30721441922969273708635883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81923845127918063223029021 30721441922969273708635883)
  ·
    refine ⟨46082162884453910562953825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30721441922969273708635883 46082162884453910562953825)
    ·
      refine ⟨34561622163340432922215369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46082162884453910562953825 34561622163340432922215369)
      ·
        refine ⟨25921216622505324691661527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34561622163340432922215369 25921216622505324691661527)
        ·
          refine ⟨38881824933757987037492291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25921216622505324691661527 38881824933757987037492291)
          ·
            refine ⟨58322737400636980556238437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38881824933757987037492291 58322737400636980556238437)
            ·
              refine ⟨10935513262619433854294707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58322737400636980556238437 10935513262619433854294707)
              ·
                refine ⟨16403269893929150781442061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10935513262619433854294707 16403269893929150781442061)
                ·
                  refine ⟨6151226210223431543040773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16403269893929150781442061 6151226210223431543040773)
                  ·
                    refine ⟨1153354914416893414320145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6151226210223431543040773 1153354914416893414320145)
                    ·
                      rfl

theorem cell22_3369226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_3369226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3369226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3369226 prefixEnd_3369226 := by exact prefixLift 3369226
  have htrace : WordTrace (prefixWord ++ tailWord_3369226) baseStart_3369226 baseEnd_3369226 := by
    simpa [prefixWord, tailWord_3369226, baseEnd_3369226] using wordTrace_append hprefix tailTrace_3369226
  have hstable : (prefixWord ++ tailWord_3369226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369226).length < 2 ^ (prefixWord ++ tailWord_3369226).sum := by decide
  have hdescent : baseEnd_3369226 < baseStart_3369226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369243 : List Nat := [1, 1, 1, 1, 1, 1, 10, 1, 1, 4]
def baseStart_3369243 : Nat := 118140960795 + 3369243 * 2 ^ 59
def prefixEnd_3369243 : Nat := 4983230072969 + 3 ^ 40 * 3369243 * 2
def baseEnd_3369243 : Nat := 1153360733864311036645093

theorem tailTrace_3369243 : CollatzResearch.WordTrace tailWord_3369243 prefixEnd_3369243 1153360733864311036645093 := by
  unfold tailWord_3369243
  simp only [CollatzResearch.WordTrace]
  refine ⟨122886387732815506737912383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81924258488543671158608255 122886387732815506737912383)
  ·
    refine ⟨184329581599223260106868575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122886387732815506737912383 184329581599223260106868575)
    ·
      refine ⟨276494372398834890160302863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184329581599223260106868575 276494372398834890160302863)
      ·
        refine ⟨414741558598252335240454295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276494372398834890160302863 414741558598252335240454295)
        ·
          refine ⟨622112337897378502860681443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414741558598252335240454295 622112337897378502860681443)
          ·
            refine ⟨933168506846067754291022165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 622112337897378502860681443 933168506846067754291022165)
            ·
              refine ⟨2733892109900589123899479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 933168506846067754291022165 2733892109900589123899479)
              ·
                refine ⟨4100838164850883685849219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2733892109900589123899479 4100838164850883685849219)
                ·
                  refine ⟨6151257247276325528773829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4100838164850883685849219 6151257247276325528773829)
                  ·
                    refine ⟨1153360733864311036645093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6151257247276325528773829 1153360733864311036645093)
                    ·
                      rfl

theorem cell22_3369243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10, 1, 1, 4].length) (baseStart_3369243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3369243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3369243 prefixEnd_3369243 := by exact prefixLift 3369243
  have htrace : WordTrace (prefixWord ++ tailWord_3369243) baseStart_3369243 baseEnd_3369243 := by
    simpa [prefixWord, tailWord_3369243, baseEnd_3369243] using wordTrace_append hprefix tailTrace_3369243
  have hstable : (prefixWord ++ tailWord_3369243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369243).length < 2 ^ (prefixWord ++ tailWord_3369243).sum := by decide
  have hdescent : baseEnd_3369243 < baseStart_3369243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369273 : List Nat := [1, 2, 1, 6, 1, 1, 3, 1, 1, 5]
def baseStart_3369273 : Nat := 118140960795 + 3369273 * 2 ^ 59
def prefixEnd_3369273 : Nat := 4983230072969 + 3 ^ 40 * 3369273 * 2
def baseEnd_3369273 : Nat := 1153371003477400958395001

theorem tailTrace_3369273 : CollatzResearch.WordTrace tailWord_3369273 prefixEnd_3369273 1153371003477400958395001 := by
  unfold tailWord_3369273
  simp only [CollatzResearch.WordTrace]
  refine ⟨122887481922706821861504473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81924987948471214574336315 122887481922706821861504473)
  ·
    refine ⟨92165611442030116396128355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122887481922706821861504473 92165611442030116396128355)
    ·
      refine ⟨138248417163045174594192533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92165611442030116396128355 138248417163045174594192533)
      ·
        refine ⟨6480394554517742559102775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 138248417163045174594192533 6480394554517742559102775)
        ·
          refine ⟨9720591831776613838654163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6480394554517742559102775 9720591831776613838654163)
          ·
            refine ⟨14580887747664920757981245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9720591831776613838654163 14580887747664920757981245)
            ·
              refine ⟨5467832905374345284242967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14580887747664920757981245 5467832905374345284242967)
              ·
                refine ⟨8201749358061517926364451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5467832905374345284242967 8201749358061517926364451)
                ·
                  refine ⟨12302624037092276889546677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8201749358061517926364451 12302624037092276889546677)
                  ·
                    refine ⟨1153371003477400958395001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12302624037092276889546677 1153371003477400958395001)
                    ·
                      rfl

theorem cell22_3369273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 1, 1, 5].length) (baseStart_3369273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3369273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3369273 prefixEnd_3369273 := by exact prefixLift 3369273
  have htrace : WordTrace (prefixWord ++ tailWord_3369273) baseStart_3369273 baseEnd_3369273 := by
    simpa [prefixWord, tailWord_3369273, baseEnd_3369273] using wordTrace_append hprefix tailTrace_3369273
  have hstable : (prefixWord ++ tailWord_3369273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369273).length < 2 ^ (prefixWord ++ tailWord_3369273).sum := by decide
  have hdescent : baseEnd_3369273 < baseStart_3369273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369316 : List Nat := [2, 3, 1, 1, 3, 1, 2, 1, 2, 6]
def baseStart_3369316 : Nat := 118140960795 + 3369316 * 2 ^ 59
def prefixEnd_3369316 : Nat := 4983230072969 + 3 ^ 40 * 3369316 * 2
def baseEnd_3369316 : Nat := 1153385723256163179569869

theorem tailTrace_3369316 : CollatzResearch.WordTrace tailWord_3369316 prefixEnd_3369316 1153385723256163179569869 := by
  unfold tailWord_3369316
  simp only [CollatzResearch.WordTrace]
  refine ⟨61444525130775520102659901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81926033507700693470213201 61444525130775520102659901)
  ·
    refine ⟨23041696924040820038497463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61444525130775520102659901 23041696924040820038497463)
    ·
      refine ⟨34562545386061230057746195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23041696924040820038497463 34562545386061230057746195)
      ·
        refine ⟨51843818079091845086619293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34562545386061230057746195 51843818079091845086619293)
        ·
          refine ⟨19441431779659441907482235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51843818079091845086619293 19441431779659441907482235)
          ·
            refine ⟨29162147669489162861223353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19441431779659441907482235 29162147669489162861223353)
            ·
              refine ⟨21871610752116872145917515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29162147669489162861223353 21871610752116872145917515)
              ·
                refine ⟨32807416128175308218876273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21871610752116872145917515 32807416128175308218876273)
                ·
                  refine ⟨24605562096131481164157205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32807416128175308218876273 24605562096131481164157205)
                  ·
                    refine ⟨1153385723256163179569869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24605562096131481164157205 1153385723256163179569869)
                    ·
                      rfl

theorem cell22_3369316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_3369316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3369316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3369316 prefixEnd_3369316 := by exact prefixLift 3369316
  have htrace : WordTrace (prefixWord ++ tailWord_3369316) baseStart_3369316 baseEnd_3369316 := by
    simpa [prefixWord, tailWord_3369316, baseEnd_3369316] using wordTrace_append hprefix tailTrace_3369316
  have hstable : (prefixWord ++ tailWord_3369316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369316).length < 2 ^ (prefixWord ++ tailWord_3369316).sum := by decide
  have hdescent : baseEnd_3369316 < baseStart_3369316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369324 : List Nat := [2, 2, 1, 1, 7, 1, 2, 1, 2, 3]
def baseStart_3369324 : Nat := 118140960795 + 3369324 * 2 ^ 59
def prefixEnd_3369324 : Nat := 4983230072969 + 3 ^ 40 * 3369324 * 2
def baseEnd_3369324 : Nat := 1153388461819653825369845

theorem tailTrace_3369324 : CollatzResearch.WordTrace tailWord_3369324 prefixEnd_3369324 1153388461819653825369845 := by
  unfold tailWord_3369324
  simp only [CollatzResearch.WordTrace]
  refine ⟨61444671022761028785805513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81926228030348038381074017 61444671022761028785805513)
  ·
    refine ⟨46083503267070771589354135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61444671022761028785805513 46083503267070771589354135)
    ·
      refine ⟨69125254900606157384031203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46083503267070771589354135 69125254900606157384031203)
      ·
        refine ⟨103687882350909236076046805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69125254900606157384031203 103687882350909236076046805)
        ·
          refine ⟨2430184742599435220532347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 103687882350909236076046805 2430184742599435220532347)
          ·
            refine ⟨3645277113899152830798521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2430184742599435220532347 3645277113899152830798521)
            ·
              refine ⟨2733957835424364623098891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3645277113899152830798521 2733957835424364623098891)
              ·
                refine ⟨4100936753136546934648337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2733957835424364623098891 4100936753136546934648337)
                ·
                  refine ⟨3075702564852410200986253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4100936753136546934648337 3075702564852410200986253)
                  ·
                    refine ⟨1153388461819653825369845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3075702564852410200986253 1153388461819653825369845)
                    ·
                      rfl

theorem cell22_3369324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 2, 1, 2, 3].length) (baseStart_3369324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3369324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3369324 prefixEnd_3369324 := by exact prefixLift 3369324
  have htrace : WordTrace (prefixWord ++ tailWord_3369324) baseStart_3369324 baseEnd_3369324 := by
    simpa [prefixWord, tailWord_3369324, baseEnd_3369324] using wordTrace_append hprefix tailTrace_3369324
  have hstable : (prefixWord ++ tailWord_3369324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369324).length < 2 ^ (prefixWord ++ tailWord_3369324).sum := by decide
  have hdescent : baseEnd_3369324 < baseStart_3369324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369331 : List Nat := [1, 1, 1, 2, 2, 1, 2, 7, 5]
def baseStart_3369331 : Nat := 118140960795 + 3369331 * 2 ^ 59
def prefixEnd_3369331 : Nat := 4983230072969 + 3 ^ 40 * 3369331 * 2
def baseEnd_3369331 : Nat := 384463619354236046814941

theorem tailTrace_3369331 : CollatzResearch.WordTrace tailWord_3369331 prefixEnd_3369331 384463619354236046814941 := by
  unfold tailWord_3369331
  simp only [CollatzResearch.WordTrace]
  refine ⟨122889597356496697767115847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81926398237664465178077231 122889597356496697767115847)
  ·
    refine ⟨184334396034745046650673771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122889597356496697767115847 184334396034745046650673771)
    ·
      refine ⟨276501594052117569976010657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184334396034745046650673771 276501594052117569976010657)
      ·
        refine ⟨207376195539088177482007993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276501594052117569976010657 207376195539088177482007993)
        ·
          refine ⟨155532146654316133111505995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207376195539088177482007993 155532146654316133111505995)
          ·
            refine ⟨233298219981474199667258993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155532146654316133111505995 233298219981474199667258993)
            ·
              refine ⟨174973664986105649750444245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 233298219981474199667258993 174973664986105649750444245)
              ·
                refine ⟨4100945273111851166026037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 174973664986105649750444245 4100945273111851166026037)
                ·
                  refine ⟨384463619354236046814941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4100945273111851166026037 384463619354236046814941)
                  ·
                    rfl

theorem cell22_3369331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 7, 5].length) (baseStart_3369331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3369331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3369331 prefixEnd_3369331 := by exact prefixLift 3369331
  have htrace : WordTrace (prefixWord ++ tailWord_3369331) baseStart_3369331 baseEnd_3369331 := by
    simpa [prefixWord, tailWord_3369331, baseEnd_3369331] using wordTrace_append hprefix tailTrace_3369331
  have hstable : (prefixWord ++ tailWord_3369331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369331).length < 2 ^ (prefixWord ++ tailWord_3369331).sum := by decide
  have hdescent : baseEnd_3369331 < baseStart_3369331 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369361 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 7, 4]
def baseStart_3369361 : Nat := 118140960795 + 3369361 * 2 ^ 59
def prefixEnd_3369361 : Nat := 4983230072969 + 3 ^ 40 * 3369361 * 2
def baseEnd_3369361 : Nat := 1153401127675798062194731

theorem tailTrace_3369361 : CollatzResearch.WordTrace tailWord_3369361 prefixEnd_3369361 1153401127675798062194731 := by
  unfold tailWord_3369361
  simp only [CollatzResearch.WordTrace]
  refine ⟨122890691546388012890707937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81927127697592008593805291 122890691546388012890707937)
  ·
    refine ⟨92168018659791009668030953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122890691546388012890707937 92168018659791009668030953)
    ·
      refine ⟨69126013994843257251023215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92168018659791009668030953 69126013994843257251023215)
      ·
        refine ⟨103689020992264885876534823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69126013994843257251023215 103689020992264885876534823)
        ·
          refine ⟨155533531488397328814802235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103689020992264885876534823 155533531488397328814802235)
          ·
            refine ⟨233300297232595993222203353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155533531488397328814802235 233300297232595993222203353)
            ·
              refine ⟨174975222924446994916652515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 233300297232595993222203353 174975222924446994916652515)
              ·
                refine ⟨262462834386670492374978773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174975222924446994916652515 262462834386670492374978773)
                ·
                  refine ⟨6151472680937589665038565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 262462834386670492374978773 6151472680937589665038565)
                  ·
                    refine ⟨1153401127675798062194731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6151472680937589665038565 1153401127675798062194731)
                    ·
                      rfl

theorem cell22_3369361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 4].length) (baseStart_3369361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3369361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3369361 prefixEnd_3369361 := by exact prefixLift 3369361
  have htrace : WordTrace (prefixWord ++ tailWord_3369361) baseStart_3369361 baseEnd_3369361 := by
    simpa [prefixWord, tailWord_3369361, baseEnd_3369361] using wordTrace_append hprefix tailTrace_3369361
  have hstable : (prefixWord ++ tailWord_3369361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369361).length < 2 ^ (prefixWord ++ tailWord_3369361).sum := by decide
  have hdescent : baseEnd_3369361 < baseStart_3369361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369378 : List Nat := [3, 3, 1, 2, 1, 1, 1, 1, 5, 4]
def baseStart_3369378 : Nat := 118140960795 + 3369378 * 2 ^ 59
def prefixEnd_3369378 : Nat := 4983230072969 + 3 ^ 40 * 3369378 * 2
def baseEnd_3369378 : Nat := 1153406947123215684519679

theorem tailTrace_3369378 : CollatzResearch.WordTrace tailWord_3369378 prefixEnd_3369378 1153406947123215684519679 := by
  unfold tailWord_3369378
  simp only [CollatzResearch.WordTrace]
  refine ⟨30722827896831606198519197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81927541058217616529384525 30722827896831606198519197)
  ·
    refine ⟨11521060461311852324444699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30722827896831606198519197 11521060461311852324444699)
    ·
      refine ⟨17281590691967778486667049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11521060461311852324444699 17281590691967778486667049)
      ·
        refine ⟨12961193018975833865000287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17281590691967778486667049 12961193018975833865000287)
        ·
          refine ⟨19441789528463750797500431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12961193018975833865000287 19441789528463750797500431)
          ·
            refine ⟨29162684292695626196250647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19441789528463750797500431 29162684292695626196250647)
            ·
              refine ⟨43744026439043439294375971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29162684292695626196250647 43744026439043439294375971)
              ·
                refine ⟨65616039658565158941563957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43744026439043439294375971 65616039658565158941563957)
                ·
                  refine ⟨6151503717990483650771621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65616039658565158941563957 6151503717990483650771621)
                  ·
                    refine ⟨1153406947123215684519679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6151503717990483650771621 1153406947123215684519679)
                    ·
                      rfl

theorem cell22_3369378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_3369378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3369378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3369378 prefixEnd_3369378 := by exact prefixLift 3369378
  have htrace : WordTrace (prefixWord ++ tailWord_3369378) baseStart_3369378 baseEnd_3369378 := by
    simpa [prefixWord, tailWord_3369378, baseEnd_3369378] using wordTrace_append hprefix tailTrace_3369378
  have hstable : (prefixWord ++ tailWord_3369378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369378).length < 2 ^ (prefixWord ++ tailWord_3369378).sum := by decide
  have hdescent : baseEnd_3369378 < baseStart_3369378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369393 : List Nat := [1, 2, 2, 4, 1, 3, 1, 2, 6]
def baseStart_3369393 : Nat := 118140960795 + 3369393 * 2 ^ 59
def prefixEnd_3369393 : Nat := 4983230072969 + 3 ^ 40 * 3369393 * 2
def baseEnd_3369393 : Nat := 384470693976586881798211

theorem tailTrace_3369393 : CollatzResearch.WordTrace tailWord_3369393 prefixEnd_3369393 384470693976586881798211 := by
  unfold tailWord_3369393
  simp only [CollatzResearch.WordTrace]
  refine ⟨122891858682272082355872833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81927905788181388237248555 122891858682272082355872833)
  ·
    refine ⟨92168894011704061766904625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122891858682272082355872833 92168894011704061766904625)
    ·
      refine ⟨69126670508778046325178469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92168894011704061766904625 69126670508778046325178469)
      ·
        refine ⟨12961250720395883685970963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69126670508778046325178469 12961250720395883685970963)
        ·
          refine ⟨19441876080593825528956445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12961250720395883685970963 19441876080593825528956445)
          ·
            refine ⟨7290703530222684573358667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19441876080593825528956445 7290703530222684573358667)
            ·
              refine ⟨10936055295334026860038001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7290703530222684573358667 10936055295334026860038001)
              ·
                refine ⟨8202041471500520145028501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10936055295334026860038001 8202041471500520145028501)
                ·
                  refine ⟨384470693976586881798211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8202041471500520145028501 384470693976586881798211)
                  ·
                    rfl

theorem cell22_3369393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 2, 6].length) (baseStart_3369393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3369393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3369393 prefixEnd_3369393 := by exact prefixLift 3369393
  have htrace : WordTrace (prefixWord ++ tailWord_3369393) baseStart_3369393 baseEnd_3369393 := by
    simpa [prefixWord, tailWord_3369393, baseEnd_3369393] using wordTrace_append hprefix tailTrace_3369393
  have hstable : (prefixWord ++ tailWord_3369393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369393).length < 2 ^ (prefixWord ++ tailWord_3369393).sum := by decide
  have hdescent : baseEnd_3369393 < baseStart_3369393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369408 : List Nat := [2, 1, 1, 2, 3, 1, 1, 4, 4, 3]
def baseStart_3369408 : Nat := 118140960795 + 3369408 * 2 ^ 59
def prefixEnd_3369408 : Nat := 4983230072969 + 3 ^ 40 * 3369408 * 2
def baseEnd_3369408 : Nat := 1153417216736305606269587

theorem tailTrace_3369408 : CollatzResearch.WordTrace tailWord_3369408 prefixEnd_3369408 1153417216736305606269587 := by
  unfold tailWord_3369408
  simp only [CollatzResearch.WordTrace]
  refine ⟨61446202888608869958834439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81928270518145159945112585 61446202888608869958834439)
  ·
    refine ⟨92169304332913304938251659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61446202888608869958834439 92169304332913304938251659)
    ·
      refine ⟨138253956499369957407377489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92169304332913304938251659 138253956499369957407377489)
      ·
        refine ⟨103690467374527468055533117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138253956499369957407377489 103690467374527468055533117)
        ·
          refine ⟨38883925265447800520824919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103690467374527468055533117 38883925265447800520824919)
          ·
            refine ⟨58325887898171700781237379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38883925265447800520824919 58325887898171700781237379)
            ·
              refine ⟨87488831847257551171856069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58325887898171700781237379 87488831847257551171856069)
              ·
                refine ⟨16404155971360790844723013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87488831847257551171856069 16404155971360790844723013)
                ·
                  refine ⟨3075779244630148283385565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16404155971360790844723013 3075779244630148283385565)
                  ·
                    refine ⟨1153417216736305606269587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3075779244630148283385565 1153417216736305606269587)
                    ·
                      rfl

theorem cell22_3369408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 4, 3].length) (baseStart_3369408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3369408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3369408 prefixEnd_3369408 := by exact prefixLift 3369408
  have htrace : WordTrace (prefixWord ++ tailWord_3369408) baseStart_3369408 baseEnd_3369408 := by
    simpa [prefixWord, tailWord_3369408, baseEnd_3369408] using wordTrace_append hprefix tailTrace_3369408
  have hstable : (prefixWord ++ tailWord_3369408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369408).length < 2 ^ (prefixWord ++ tailWord_3369408).sum := by decide
  have hdescent : baseEnd_3369408 < baseStart_3369408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369412 : List Nat := [2, 3, 3, 2, 2, 1, 1, 3, 1, 4]
def baseStart_3369412 : Nat := 118140960795 + 3369412 * 2 ^ 59
def prefixEnd_3369412 : Nat := 4983230072969 + 3 ^ 40 * 3369412 * 2
def baseEnd_3369412 : Nat := 1153418586018050929169575

theorem tailTrace_3369412 : CollatzResearch.WordTrace tailWord_3369412 prefixEnd_3369412 1153418586018050929169575 := by
  unfold tailWord_3369412
  simp only [CollatzResearch.WordTrace]
  refine ⟨61446275834601624300407245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81928367779468832400542993 61446275834601624300407245)
  ·
    refine ⟨23042353437975609112652717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61446275834601624300407245 23042353437975609112652717)
    ·
      refine ⟨8640882539240853417244769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23042353437975609112652717 8640882539240853417244769)
      ·
        refine ⟨6480661904430640062933577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8640882539240853417244769 6480661904430640062933577)
        ·
          refine ⟨4860496428322980047200183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6480661904430640062933577 4860496428322980047200183)
          ·
            refine ⟨7290744642484470070800275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4860496428322980047200183 7290744642484470070800275)
            ·
              refine ⟨10936116963726705106200413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7290744642484470070800275 10936116963726705106200413)
              ·
                refine ⟨4101043861397514414825155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10936116963726705106200413 4101043861397514414825155)
                ·
                  refine ⟨6151565792096271622237733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4101043861397514414825155 6151565792096271622237733)
                  ·
                    refine ⟨1153418586018050929169575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6151565792096271622237733 1153418586018050929169575)
                    ·
                      rfl

theorem cell22_3369412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_3369412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3369412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3369412 prefixEnd_3369412 := by exact prefixLift 3369412
  have htrace : WordTrace (prefixWord ++ tailWord_3369412) baseStart_3369412 baseEnd_3369412 := by
    simpa [prefixWord, tailWord_3369412, baseEnd_3369412] using wordTrace_append hprefix tailTrace_3369412
  have hstable : (prefixWord ++ tailWord_3369412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369412).length < 2 ^ (prefixWord ++ tailWord_3369412).sum := by decide
  have hdescent : baseEnd_3369412 < baseStart_3369412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369461 : List Nat := [1, 3, 5, 1, 3, 1, 1, 3, 4]
def baseStart_3369461 : Nat := 118140960795 + 3369461 * 2 ^ 59
def prefixEnd_3369461 : Nat := 4983230072969 + 3 ^ 40 * 3369461 * 2
def baseEnd_3369461 : Nat := 384478453239810378231475

theorem tailTrace_3369461 : CollatzResearch.WordTrace tailWord_3369461 prefixEnd_3369461 384478453239810378231475 := by
  unfold tailWord_3369461
  simp only [CollatzResearch.WordTrace]
  refine ⟨122894338846025729969348237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81929559230683819979565491 122894338846025729969348237)
  ·
    refine ⟨46085377067259648738505589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122894338846025729969348237 46085377067259648738505589)
    ·
      refine ⟨4320504100055592069234899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46085377067259648738505589 4320504100055592069234899)
      ·
        refine ⟨6480756150083388103852349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4320504100055592069234899 6480756150083388103852349)
        ·
          refine ⟨2430283556281270538944631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6480756150083388103852349 2430283556281270538944631)
          ·
            refine ⟨3645425334421905808416947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2430283556281270538944631 3645425334421905808416947)
            ·
              refine ⟨5468138001632858712625421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3645425334421905808416947 5468138001632858712625421)
              ·
                refine ⟨2050551750612322017234533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5468138001632858712625421 2050551750612322017234533)
                ·
                  refine ⟨384478453239810378231475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2050551750612322017234533 384478453239810378231475)
                  ·
                    rfl

theorem cell22_3369461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 3, 4].length) (baseStart_3369461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3369461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3369461 prefixEnd_3369461 := by exact prefixLift 3369461
  have htrace : WordTrace (prefixWord ++ tailWord_3369461) baseStart_3369461 baseEnd_3369461 := by
    simpa [prefixWord, tailWord_3369461, baseEnd_3369461] using wordTrace_append hprefix tailTrace_3369461
  have hstable : (prefixWord ++ tailWord_3369461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369461).length < 2 ^ (prefixWord ++ tailWord_3369461).sum := by decide
  have hdescent : baseEnd_3369461 < baseStart_3369461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369478 : List Nat := [6, 2, 1, 1, 1, 2, 3, 2, 4]
def baseStart_3369478 : Nat := 118140960795 + 3369478 * 2 ^ 59
def prefixEnd_3369478 : Nat := 4983230072969 + 3 ^ 40 * 3369478 * 2
def baseEnd_3369478 : Nat := 384480393055616252339791

theorem tailTrace_3369478 : CollatzResearch.WordTrace tailWord_3369478 prefixEnd_3369478 384480393055616252339791 := by
  unfold tailWord_3369478
  simp only [CollatzResearch.WordTrace]
  refine ⟨3840467465217629433522409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 81929972591309427915144725 3840467465217629433522409)
  ·
    refine ⟨2880350598913222075141807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3840467465217629433522409 2880350598913222075141807)
    ·
      refine ⟨4320525898369833112712711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2880350598913222075141807 4320525898369833112712711)
      ·
        refine ⟨6480788847554749669069067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4320525898369833112712711 6480788847554749669069067)
        ·
          refine ⟨9721183271332124503603601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6480788847554749669069067 9721183271332124503603601)
          ·
            refine ⟨7290887453499093377702701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9721183271332124503603601 7290887453499093377702701)
            ·
              refine ⟨2734082795062160016638513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7290887453499093377702701 2734082795062160016638513)
              ·
                refine ⟨2050562096296620012478885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2734082795062160016638513 2050562096296620012478885)
                ·
                  refine ⟨384480393055616252339791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2050562096296620012478885 384480393055616252339791)
                  ·
                    rfl

theorem cell22_3369478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_3369478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3369478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3369478 prefixEnd_3369478 := by exact prefixLift 3369478
  have htrace : WordTrace (prefixWord ++ tailWord_3369478) baseStart_3369478 baseEnd_3369478 := by
    simpa [prefixWord, tailWord_3369478, baseEnd_3369478] using wordTrace_append hprefix tailTrace_3369478
  have hstable : (prefixWord ++ tailWord_3369478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369478).length < 2 ^ (prefixWord ++ tailWord_3369478).sum := by decide
  have hdescent : baseEnd_3369478 < baseStart_3369478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369483 : List Nat := [1, 1, 1, 1, 7, 1, 2, 1, 7]
def baseStart_3369483 : Nat := 118140960795 + 3369483 * 2 ^ 59
def prefixEnd_3369483 : Nat := 4983230072969 + 3 ^ 40 * 3369483 * 2
def baseEnd_3369483 : Nat := 384480963589676803548119

theorem tailTrace_3369483 : CollatzResearch.WordTrace tailWord_3369483 prefixEnd_3369483 384480963589676803548119 := by
  unfold tailWord_3369483
  simp only [CollatzResearch.WordTrace]
  refine ⟨122895141251946027726649103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81930094167964018484432735 122895141251946027726649103)
  ·
    refine ⟨184342711877919041589973655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122895141251946027726649103 184342711877919041589973655)
    ·
      refine ⟨276514067816878562384960483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184342711877919041589973655 276514067816878562384960483)
      ·
        refine ⟨414771101725317843577440725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276514067816878562384960483 414771101725317843577440725)
        ·
          refine ⟨9721197696687136958846267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 414771101725317843577440725 9721197696687136958846267)
          ·
            refine ⟨14581796545030705438269401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9721197696687136958846267 14581796545030705438269401)
            ·
              refine ⟨10936347408773029078702051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14581796545030705438269401 10936347408773029078702051)
              ·
                refine ⟨16404521113159543618053077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10936347408773029078702051 16404521113159543618053077)
                ·
                  refine ⟨384480963589676803548119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16404521113159543618053077 384480963589676803548119)
                  ·
                    rfl

theorem cell22_3369483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 7].length) (baseStart_3369483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3369483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3369483 prefixEnd_3369483 := by exact prefixLift 3369483
  have htrace : WordTrace (prefixWord ++ tailWord_3369483) baseStart_3369483 baseEnd_3369483 := by
    simpa [prefixWord, tailWord_3369483, baseEnd_3369483] using wordTrace_append hprefix tailTrace_3369483
  have hstable : (prefixWord ++ tailWord_3369483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369483).length < 2 ^ (prefixWord ++ tailWord_3369483).sum := by decide
  have hdescent : baseEnd_3369483 < baseStart_3369483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369498 : List Nat := [3, 1, 1, 3, 1, 1, 2, 3, 2, 5]
def baseStart_3369498 : Nat := 118140960795 + 3369498 * 2 ^ 59
def prefixEnd_3369498 : Nat := 4983230072969 + 3 ^ 40 * 3369498 * 2
def baseEnd_3369498 : Nat := 1153448025575575371519311

theorem tailTrace_3369498 : CollatzResearch.WordTrace tailWord_3369498 prefixEnd_3369498 1153448025575575371519311 := by
  unfold tailWord_3369498
  simp only [CollatzResearch.WordTrace]
  refine ⟨30723922086722921322111287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81930458897927790192296765 30723922086722921322111287)
  ·
    refine ⟨46085883130084381983166931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30723922086722921322111287 46085883130084381983166931)
    ·
      refine ⟨69128824695126572974750397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46085883130084381983166931 69128824695126572974750397)
      ·
        refine ⟨25923309260672464865531399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69128824695126572974750397 25923309260672464865531399)
        ·
          refine ⟨38884963891008697298297099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25923309260672464865531399 38884963891008697298297099)
          ·
            refine ⟨58327445836513045947445649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38884963891008697298297099 58327445836513045947445649)
            ·
              refine ⟨43745584377384784460584237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58327445836513045947445649 43745584377384784460584237)
              ·
                refine ⟨16404594141519294172719089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43745584377384784460584237 16404594141519294172719089)
                ·
                  refine ⟨12303445606139470629539317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16404594141519294172719089 12303445606139470629539317)
                  ·
                    refine ⟨1153448025575575371519311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12303445606139470629539317 1153448025575575371519311)
                    ·
                      rfl

theorem cell22_3369498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 2, 5].length) (baseStart_3369498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3369498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3369498 prefixEnd_3369498 := by exact prefixLift 3369498
  have htrace : WordTrace (prefixWord ++ tailWord_3369498) baseStart_3369498 baseEnd_3369498 := by
    simpa [prefixWord, tailWord_3369498, baseEnd_3369498] using wordTrace_append hprefix tailTrace_3369498
  have hstable : (prefixWord ++ tailWord_3369498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369498).length < 2 ^ (prefixWord ++ tailWord_3369498).sum := by decide
  have hdescent : baseEnd_3369498 < baseStart_3369498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369500 : List Nat := [2, 2, 3, 1, 2, 3, 1, 3, 5]
def baseStart_3369500 : Nat := 118140960795 + 3369500 * 2 ^ 59
def prefixEnd_3369500 : Nat := 4983230072969 + 3 ^ 40 * 3369500 * 2
def baseEnd_3369500 : Nat := 384482903405482677656435

theorem tailTrace_3369500 : CollatzResearch.WordTrace tailWord_3369500 prefixEnd_3369500 384482903405482677656435 := by
  unfold tailWord_3369500
  simp only [CollatzResearch.WordTrace]
  refine ⟨61447880646442219815008977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81930507528589626420011969 61447880646442219815008977)
  ·
    refine ⟨46085910484831664861256733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61447880646442219815008977 46085910484831664861256733)
    ·
      refine ⟨17282216431811874322971275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46085910484831664861256733 17282216431811874322971275)
      ·
        refine ⟨25923324647717811484456913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17282216431811874322971275 25923324647717811484456913)
        ·
          refine ⟨19442493485788358613342685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25923324647717811484456913 19442493485788358613342685)
          ·
            refine ⟨7290935057170634480003507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19442493485788358613342685 7290935057170634480003507)
            ·
              refine ⟨10936402585755951720005261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7290935057170634480003507 10936402585755951720005261)
              ·
                refine ⟨4101150969658481895001973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10936402585755951720005261 4101150969658481895001973)
                ·
                  refine ⟨384482903405482677656435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4101150969658481895001973 384482903405482677656435)
                  ·
                    rfl

theorem cell22_3369500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 3, 5].length) (baseStart_3369500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3369500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3369500 prefixEnd_3369500 := by exact prefixLift 3369500
  have htrace : WordTrace (prefixWord ++ tailWord_3369500) baseStart_3369500 baseEnd_3369500 := by
    simpa [prefixWord, tailWord_3369500, baseEnd_3369500] using wordTrace_append hprefix tailTrace_3369500
  have hstable : (prefixWord ++ tailWord_3369500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369500).length < 2 ^ (prefixWord ++ tailWord_3369500).sum := by decide
  have hdescent : baseEnd_3369500 < baseStart_3369500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369534 : List Nat := [4, 2, 1, 4, 1, 1, 2, 2, 5]
def baseStart_3369534 : Nat := 118140960795 + 3369534 * 2 ^ 59
def prefixEnd_3369534 : Nat := 4983230072969 + 3 ^ 40 * 3369534 * 2
def baseEnd_3369534 : Nat := 384486783037094425873067

theorem tailTrace_3369534 : CollatzResearch.WordTrace tailWord_3369534 prefixEnd_3369534 384486783037094425873067 := by
  unfold tailWord_3369534
  simp only [CollatzResearch.WordTrace]
  refine ⟨15362125171845157929594457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81931334249840842291170437 15362125171845157929594457)
  ·
    refine ⟨11521593878883868447195843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15362125171845157929594457 11521593878883868447195843)
    ·
      refine ⟨17282390818325802670793765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11521593878883868447195843 17282390818325802670793765)
      ·
        refine ⟨3240448278436088000773831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17282390818325802670793765 3240448278436088000773831)
        ·
          refine ⟨4860672417654132001160747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3240448278436088000773831 4860672417654132001160747)
          ·
            refine ⟨7291008626481198001741121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4860672417654132001160747 7291008626481198001741121)
            ·
              refine ⟨5468256469860898501305841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7291008626481198001741121 5468256469860898501305841)
              ·
                refine ⟨4101192352395673875979381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5468256469860898501305841 4101192352395673875979381)
                ·
                  refine ⟨384486783037094425873067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4101192352395673875979381 384486783037094425873067)
                  ·
                    rfl

theorem cell22_3369534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_3369534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3369534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3369534 prefixEnd_3369534 := by exact prefixLift 3369534
  have htrace : WordTrace (prefixWord ++ tailWord_3369534) baseStart_3369534 baseEnd_3369534 := by
    simpa [prefixWord, tailWord_3369534, baseEnd_3369534] using wordTrace_append hprefix tailTrace_3369534
  have hstable : (prefixWord ++ tailWord_3369534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369534).length < 2 ^ (prefixWord ++ tailWord_3369534).sum := by decide
  have hdescent : baseEnd_3369534 < baseStart_3369534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369603 : List Nat := [1, 1, 1, 3, 3, 1, 2, 1, 1, 8]
def baseStart_3369603 : Nat := 118140960795 + 3369603 * 2 ^ 59
def prefixEnd_3369603 : Nat := 4983230072969 + 3 ^ 40 * 3369603 * 2
def baseEnd_3369603 : Nat := 1153483969221390097643989

theorem tailTrace_3369603 : CollatzResearch.WordTrace tailWord_3369603 prefixEnd_3369603 1153483969221390097643989 := by
  unfold tailWord_3369603
  simp only [CollatzResearch.WordTrace]
  refine ⟨122899518011511288221017463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81933012007674192147344975 122899518011511288221017463)
  ·
    refine ⟨184349277017266932331526195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122899518011511288221017463 184349277017266932331526195)
    ·
      refine ⟨276523915525900398497289293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184349277017266932331526195 276523915525900398497289293)
      ·
        refine ⟨103696468322212649436483485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 276523915525900398497289293 103696468322212649436483485)
        ·
          refine ⟨38886175620829743538681307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103696468322212649436483485 38886175620829743538681307)
          ·
            refine ⟨58329263431244615308021961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38886175620829743538681307 58329263431244615308021961)
            ·
              refine ⟨43746947573433461481016471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58329263431244615308021961 43746947573433461481016471)
              ·
                refine ⟨65620421360150192221524707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43746947573433461481016471 65620421360150192221524707)
                ·
                  refine ⟨98430632040225288332287061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65620421360150192221524707 98430632040225288332287061)
                  ·
                    refine ⟨1153483969221390097643989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 98430632040225288332287061 1153483969221390097643989)
                    ·
                      rfl

theorem cell22_3369603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 8].length) (baseStart_3369603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3369603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3369603 prefixEnd_3369603 := by exact prefixLift 3369603
  have htrace : WordTrace (prefixWord ++ tailWord_3369603) baseStart_3369603 baseEnd_3369603 := by
    simpa [prefixWord, tailWord_3369603, baseEnd_3369603] using wordTrace_append hprefix tailTrace_3369603
  have hstable : (prefixWord ++ tailWord_3369603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369603).length < 2 ^ (prefixWord ++ tailWord_3369603).sum := by decide
  have hdescent : baseEnd_3369603 < baseStart_3369603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369695 : List Nat := [1, 1, 2, 3, 2, 3, 1, 1, 3, 5]
def baseStart_3369695 : Nat := 118140960795 + 3369695 * 2 ^ 59
def prefixEnd_3369695 : Nat := 4983230072969 + 3 ^ 40 * 3369695 * 2
def baseEnd_3369695 : Nat := 1153515462701532524343707

theorem tailTrace_3369695 : CollatzResearch.WordTrace tailWord_3369695 prefixEnd_3369695 1153515462701532524343707 := by
  unfold tailWord_3369695
  simp only [CollatzResearch.WordTrace]
  refine ⟨122902873527177987933366539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81935249018118658622244359 122902873527177987933366539)
  ·
    refine ⟨184354310290766981900049809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122902873527177987933366539 184354310290766981900049809)
    ·
      refine ⟨138265732718075236425037357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184354310290766981900049809 138265732718075236425037357)
      ·
        refine ⟨51849649769278213659389009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138265732718075236425037357 51849649769278213659389009)
        ·
          refine ⟨38887237326958660244541757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51849649769278213659389009 38887237326958660244541757)
          ·
            refine ⟨14582713997609497591703159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38887237326958660244541757 14582713997609497591703159)
            ·
              refine ⟨21874070996414246387554739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14582713997609497591703159 21874070996414246387554739)
              ·
                refine ⟨32811106494621369581332109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21874070996414246387554739 32811106494621369581332109)
                ·
                  refine ⟨12304164935483013592999541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32811106494621369581332109 12304164935483013592999541)
                  ·
                    refine ⟨1153515462701532524343707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12304164935483013592999541 1153515462701532524343707)
                    ·
                      rfl

theorem cell22_3369695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 3, 5].length) (baseStart_3369695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3369695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3369695 prefixEnd_3369695 := by exact prefixLift 3369695
  have htrace : WordTrace (prefixWord ++ tailWord_3369695) baseStart_3369695 baseEnd_3369695 := by
    simpa [prefixWord, tailWord_3369695, baseEnd_3369695] using wordTrace_append hprefix tailTrace_3369695
  have hstable : (prefixWord ++ tailWord_3369695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369695).length < 2 ^ (prefixWord ++ tailWord_3369695).sum := by decide
  have hdescent : baseEnd_3369695 < baseStart_3369695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369714 : List Nat := [3, 2, 1, 3, 1, 3, 1, 4, 4]
def baseStart_3369714 : Nat := 118140960795 + 3369714 * 2 ^ 59
def prefixEnd_3369714 : Nat := 4983230072969 + 3 ^ 40 * 3369714 * 2
def baseEnd_3369714 : Nat := 384507322263274269372883

theorem tailTrace_3369714 : CollatzResearch.WordTrace tailWord_3369714 prefixEnd_3369714 384507322263274269372883 := by
  unfold tailWord_3369714
  simp only [CollatzResearch.WordTrace]
  refine ⟨30725891628527288544577049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81935711009406102785538797 30725891628527288544577049)
  ·
    refine ⟨23044418721395466408432787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30725891628527288544577049 23044418721395466408432787)
    ·
      refine ⟨34566628082093199612649181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23044418721395466408432787 34566628082093199612649181)
      ·
        refine ⟨12962485530784949854743443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34566628082093199612649181 12962485530784949854743443)
        ·
          refine ⟨19443728296177424782115165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12962485530784949854743443 19443728296177424782115165)
          ·
            refine ⟨7291398111066534293293187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19443728296177424782115165 7291398111066534293293187)
            ·
              refine ⟨10937097166599801439939781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7291398111066534293293187 10937097166599801439939781)
              ·
                refine ⟨2050705718737462769988709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10937097166599801439939781 2050705718737462769988709)
                ·
                  refine ⟨384507322263274269372883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2050705718737462769988709 384507322263274269372883)
                  ·
                    rfl

theorem cell22_3369714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 4, 4].length) (baseStart_3369714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3369714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3369714 prefixEnd_3369714 := by exact prefixLift 3369714
  have htrace : WordTrace (prefixWord ++ tailWord_3369714) baseStart_3369714 baseEnd_3369714 := by
    simpa [prefixWord, tailWord_3369714, baseEnd_3369714] using wordTrace_append hprefix tailTrace_3369714
  have hstable : (prefixWord ++ tailWord_3369714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369714).length < 2 ^ (prefixWord ++ tailWord_3369714).sum := by decide
  have hdescent : baseEnd_3369714 < baseStart_3369714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369793 : List Nat := [1, 2, 5, 3, 2, 1, 2, 6]
def baseStart_3369793 : Nat := 118140960795 + 3369793 * 2 ^ 59
def prefixEnd_3369793 : Nat := 4983230072969 + 3 ^ 40 * 3369793 * 2
def baseEnd_3369793 : Nat := 128172112233810326154823

theorem tailTrace_3369793 : CollatzResearch.WordTrace tailWord_3369793 prefixEnd_3369793 128172112233810326154823 := by
  unfold tailWord_3369793
  simp only [CollatzResearch.WordTrace]
  refine ⟨122906447880822950670434033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81937631920548633780289355 122906447880822950670434033)
  ·
    refine ⟨92179835910617213002825525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122906447880822950670434033 92179835910617213002825525)
    ·
      refine ⟨8641859616620363719014893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92179835910617213002825525 8641859616620363719014893)
      ·
        refine ⟨3240697356232636394630585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8641859616620363719014893 3240697356232636394630585)
        ·
          refine ⟨2430523017174477295972939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3240697356232636394630585 2430523017174477295972939)
          ·
            refine ⟨3645784525761715943959409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2430523017174477295972939 3645784525761715943959409)
            ·
              refine ⟨2734338394321286957969557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3645784525761715943959409 2734338394321286957969557)
              ·
                refine ⟨128172112233810326154823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2734338394321286957969557 128172112233810326154823)
                ·
                  rfl

theorem cell22_3369793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 2, 6].length) (baseStart_3369793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3369793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3369793 prefixEnd_3369793 := by exact prefixLift 3369793
  have htrace : WordTrace (prefixWord ++ tailWord_3369793) baseStart_3369793 baseEnd_3369793 := by
    simpa [prefixWord, tailWord_3369793, baseEnd_3369793] using wordTrace_append hprefix tailTrace_3369793
  have hstable : (prefixWord ++ tailWord_3369793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369793).length < 2 ^ (prefixWord ++ tailWord_3369793).sum := by decide
  have hdescent : baseEnd_3369793 < baseStart_3369793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369838 : List Nat := [4, 1, 2, 3, 2, 2, 2, 1, 5]
def baseStart_3369838 : Nat := 118140960795 + 3369838 * 2 ^ 59
def prefixEnd_3369838 : Nat := 4983230072969 + 3 ^ 40 * 3369838 * 2
def baseEnd_3369838 : Nat := 384521471507975939339423

theorem tailTrace_3369838 : CollatzResearch.WordTrace tailWord_3369838 prefixEnd_3369838 384521471507975939339423 := by
  unfold tailWord_3369838
  simp only [CollatzResearch.WordTrace]
  refine ⟨15363511145707490419477771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81938726110439948903881445 15363511145707490419477771)
  ·
    refine ⟨23045266718561235629216657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15363511145707490419477771 23045266718561235629216657)
    ·
      refine ⟨17283950038920926721912493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23045266718561235629216657 17283950038920926721912493)
      ·
        refine ⟨6481481264595347520717185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17283950038920926721912493 6481481264595347520717185)
        ·
          refine ⟨4861110948446510640537889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6481481264595347520717185 4861110948446510640537889)
          ·
            refine ⟨3645833211334882980403417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4861110948446510640537889 3645833211334882980403417)
            ·
              refine ⟨2734374908501162235302563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3645833211334882980403417 2734374908501162235302563)
              ·
                refine ⟨4101562362751743352953845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2734374908501162235302563 4101562362751743352953845)
                ·
                  refine ⟨384521471507975939339423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4101562362751743352953845 384521471507975939339423)
                  ·
                    rfl

theorem cell22_3369838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2, 1, 5].length) (baseStart_3369838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3369838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3369838 prefixEnd_3369838 := by exact prefixLift 3369838
  have htrace : WordTrace (prefixWord ++ tailWord_3369838) baseStart_3369838 baseEnd_3369838 := by
    simpa [prefixWord, tailWord_3369838, baseEnd_3369838] using wordTrace_append hprefix tailTrace_3369838
  have hstable : (prefixWord ++ tailWord_3369838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369838).length < 2 ^ (prefixWord ++ tailWord_3369838).sum := by decide
  have hdescent : baseEnd_3369838 < baseStart_3369838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369864 : List Nat := [2, 1, 3, 3, 2, 2, 1, 2, 1, 5]
def baseStart_3369864 : Nat := 118140960795 + 3369864 * 2 ^ 59
def prefixEnd_3369864 : Nat := 4983230072969 + 3 ^ 40 * 3369864 * 2
def baseEnd_3369864 : Nat := 1153573314855272416868189

theorem tailTrace_3369864 : CollatzResearch.WordTrace tailWord_3369864 prefixEnd_3369864 1153573314855272416868189 := by
  unfold tailWord_3369864
  simp only [CollatzResearch.WordTrace]
  refine ⟨61454518731782864898134323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81939358309043819864179097 61454518731782864898134323)
  ·
    refine ⟨92181778097674297347201485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61454518731782864898134323 92181778097674297347201485)
    ·
      refine ⟨34568166786627861505200557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92181778097674297347201485 34568166786627861505200557)
      ·
        refine ⟨12963062544985448064450209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34568166786627861505200557 12963062544985448064450209)
        ·
          refine ⟨9722296908739086048337657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12963062544985448064450209 9722296908739086048337657)
          ·
            refine ⟨7291722681554314536253243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9722296908739086048337657 7291722681554314536253243)
            ·
              refine ⟨10937584022331471804379865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7291722681554314536253243 10937584022331471804379865)
              ·
                refine ⟨8203188016748603853284899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10937584022331471804379865 8203188016748603853284899)
                ·
                  refine ⟨12304782025122905779927349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8203188016748603853284899 12304782025122905779927349)
                  ·
                    refine ⟨1153573314855272416868189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12304782025122905779927349 1153573314855272416868189)
                    ·
                      rfl

theorem cell22_3369864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_3369864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3369864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3369864 prefixEnd_3369864 := by exact prefixLift 3369864
  have htrace : WordTrace (prefixWord ++ tailWord_3369864) baseStart_3369864 baseEnd_3369864 := by
    simpa [prefixWord, tailWord_3369864, baseEnd_3369864] using wordTrace_append hprefix tailTrace_3369864
  have hstable : (prefixWord ++ tailWord_3369864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369864).length < 2 ^ (prefixWord ++ tailWord_3369864).sum := by decide
  have hdescent : baseEnd_3369864 < baseStart_3369864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369937 : List Nat := [1, 2, 2, 1, 2, 1, 3, 1, 4, 5]
def baseStart_3369937 : Nat := 118140960795 + 3369937 * 2 ^ 59
def prefixEnd_3369937 : Nat := 4983230072969 + 3 ^ 40 * 3369937 * 2
def baseEnd_3369937 : Nat := 1153598304247124559792965

theorem tailTrace_3369937 : CollatzResearch.WordTrace tailWord_3369937 prefixEnd_3369937 1153598304247124559792965 := by
  unfold tailWord_3369937
  simp only [CollatzResearch.WordTrace]
  refine ⟨122911699992301263263676065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81941133328200842175784043 122911699992301263263676065)
  ·
    refine ⟨92183774994225947447757049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122911699992301263263676065 92183774994225947447757049)
    ·
      refine ⟨69137831245669460585817787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92183774994225947447757049 69137831245669460585817787)
      ·
        refine ⟨103706746868504190878726681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69137831245669460585817787 103706746868504190878726681)
        ·
          refine ⟨77780060151378143159045011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103706746868504190878726681 77780060151378143159045011)
          ·
            refine ⟨116670090227067214738567517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77780060151378143159045011 116670090227067214738567517)
            ·
              refine ⟨43751283835150205526962819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116670090227067214738567517 43751283835150205526962819)
              ·
                refine ⟨65626925752725308290444229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43751283835150205526962819 65626925752725308290444229)
                ·
                  refine ⟨12305048578635995304458293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65626925752725308290444229 12305048578635995304458293)
                  ·
                    refine ⟨1153598304247124559792965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12305048578635995304458293 1153598304247124559792965)
                    ·
                      rfl

theorem cell22_3369937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4, 5].length) (baseStart_3369937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3369937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3369937 prefixEnd_3369937 := by exact prefixLift 3369937
  have htrace : WordTrace (prefixWord ++ tailWord_3369937) baseStart_3369937 baseEnd_3369937 := by
    simpa [prefixWord, tailWord_3369937, baseEnd_3369937] using wordTrace_append hprefix tailTrace_3369937
  have hstable : (prefixWord ++ tailWord_3369937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369937).length < 2 ^ (prefixWord ++ tailWord_3369937).sum := by decide
  have hdescent : baseEnd_3369937 < baseStart_3369937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370136 : List Nat := [2, 1, 2, 4, 2, 1, 2, 2, 6]
def baseStart_3370136 : Nat := 118140960795 + 3370136 * 2 ^ 59
def prefixEnd_3370136 : Nat := 4983230072969 + 3 ^ 40 * 3370136 * 2
def baseEnd_3370136 : Nat := 384555475337984791355785

theorem tailTrace_3370136 : CollatzResearch.WordTrace tailWord_3370136 prefixEnd_3370136 384555475337984791355785 := by
  unfold tailWord_3370136
  simp only [CollatzResearch.WordTrace]
  refine ⟨61459479059290160125085131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81945972079053546833446841 61459479059290160125085131)
  ·
    refine ⟨92189218588935240187627697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61459479059290160125085131 92189218588935240187627697)
    ·
      refine ⟨69141913941701430140720773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92189218588935240187627697 69141913941701430140720773)
      ·
        refine ⟨12964108864069018151385145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69141913941701430140720773 12964108864069018151385145)
        ·
          refine ⟨9723081648051763613538859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12964108864069018151385145 9723081648051763613538859)
          ·
            refine ⟨14584622472077645420308289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9723081648051763613538859 14584622472077645420308289)
            ·
              refine ⟨10938466854058234065231217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14584622472077645420308289 10938466854058234065231217)
              ·
                refine ⟨8203850140543675548923413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10938466854058234065231217 8203850140543675548923413)
                ·
                  refine ⟨384555475337984791355785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8203850140543675548923413 384555475337984791355785)
                  ·
                    rfl

theorem cell22_3370136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 2, 6].length) (baseStart_3370136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3370136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3370136 prefixEnd_3370136 := by exact prefixLift 3370136
  have htrace : WordTrace (prefixWord ++ tailWord_3370136) baseStart_3370136 baseEnd_3370136 := by
    simpa [prefixWord, tailWord_3370136, baseEnd_3370136] using wordTrace_append hprefix tailTrace_3370136
  have hstable : (prefixWord ++ tailWord_3370136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370136).length < 2 ^ (prefixWord ++ tailWord_3370136).sum := by decide
  have hdescent : baseEnd_3370136 < baseStart_3370136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370138 : List Nat := [3, 1, 1, 5, 1, 1, 1, 4, 1, 4]
def baseStart_3370138 : Nat := 118140960795 + 3370138 * 2 ^ 59
def prefixEnd_3370138 : Nat := 4983230072969 + 3 ^ 40 * 3370138 * 2
def baseEnd_3370138 : Nat := 1153667110654827035517349

theorem tailTrace_3370138 : CollatzResearch.WordTrace tailWord_3370138 prefixEnd_3370138 1153667110654827035517349 := by
  unfold tailWord_3370138
  simp only [CollatzResearch.WordTrace]
  refine ⟨30729757766143268647935767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81946020709715383061162045 30729757766143268647935767)
  ·
    refine ⟨46094636649214902971903651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30729757766143268647935767 46094636649214902971903651)
    ·
      refine ⟨69141954973822354457855477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46094636649214902971903651 69141954973822354457855477)
      ·
        refine ⟨6482058278795845730423951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69141954973822354457855477 6482058278795845730423951)
        ·
          refine ⟨9723087418193768595635927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6482058278795845730423951 9723087418193768595635927)
          ·
            refine ⟨14584631127290652893453891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9723087418193768595635927 14584631127290652893453891)
            ·
              refine ⟨21876946690935979340180837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14584631127290652893453891 21876946690935979340180837)
              ·
                refine ⟨4101927504550496126283907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21876946690935979340180837 4101927504550496126283907)
                ·
                  refine ⟨6152891256825744189425861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4101927504550496126283907 6152891256825744189425861)
                  ·
                    refine ⟨1153667110654827035517349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6152891256825744189425861 1153667110654827035517349)
                    ·
                      rfl

theorem cell22_3370138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 4, 1, 4].length) (baseStart_3370138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3370138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3370138 prefixEnd_3370138 := by exact prefixLift 3370138
  have htrace : WordTrace (prefixWord ++ tailWord_3370138) baseStart_3370138 baseEnd_3370138 := by
    simpa [prefixWord, tailWord_3370138, baseEnd_3370138] using wordTrace_append hprefix tailTrace_3370138
  have hstable : (prefixWord ++ tailWord_3370138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370138).length < 2 ^ (prefixWord ++ tailWord_3370138).sum := by decide
  have hdescent : baseEnd_3370138 < baseStart_3370138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370179 : List Nat := [1, 1, 1, 3, 1, 1, 1, 4, 2, 7]
def baseStart_3370179 : Nat := 118140960795 + 3370179 * 2 ^ 59
def prefixEnd_3370179 : Nat := 4983230072969 + 3 ^ 40 * 3370179 * 2
def baseEnd_3370179 : Nat := 1153681145792716595242223

theorem tailTrace_3370179 : CollatzResearch.WordTrace tailWord_3370179 prefixEnd_3370179 1153681145792716595242223 := by
  unfold tailWord_3370179
  simp only [CollatzResearch.WordTrace]
  refine ⟨122920526457424538593985591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81947017638283025729323727 122920526457424538593985591)
  ·
    refine ⟨184380789686136807890978387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122920526457424538593985591 184380789686136807890978387)
    ·
      refine ⟨276571184529205211836467581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184380789686136807890978387 276571184529205211836467581)
      ·
        refine ⟨103714194198451954438675343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 276571184529205211836467581 103714194198451954438675343)
        ·
          refine ⟨155571291297677931658013015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103714194198451954438675343 155571291297677931658013015)
          ·
            refine ⟨233356936946516897487019523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155571291297677931658013015 233356936946516897487019523)
            ·
              refine ⟨350035405419775346230529285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233356936946516897487019523 350035405419775346230529285)
              ·
                refine ⟨65631638516207877418224241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 350035405419775346230529285 65631638516207877418224241)
                ·
                  refine ⟨49223728887155908063668181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65631638516207877418224241 49223728887155908063668181)
                  ·
                    refine ⟨1153681145792716595242223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49223728887155908063668181 1153681145792716595242223)
                    ·
                      rfl

theorem cell22_3370179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 7].length) (baseStart_3370179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3370179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3370179 prefixEnd_3370179 := by exact prefixLift 3370179
  have htrace : WordTrace (prefixWord ++ tailWord_3370179) baseStart_3370179 baseEnd_3370179 := by
    simpa [prefixWord, tailWord_3370179, baseEnd_3370179] using wordTrace_append hprefix tailTrace_3370179
  have hstable : (prefixWord ++ tailWord_3370179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370179).length < 2 ^ (prefixWord ++ tailWord_3370179).sum := by decide
  have hdescent : baseEnd_3370179 < baseStart_3370179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370189 : List Nat := [1, 6, 2, 2, 1, 2, 1, 2, 1, 4]
def baseStart_3370189 : Nat := 118140960795 + 3370189 * 2 ^ 59
def prefixEnd_3370189 : Nat := 4983230072969 + 3 ^ 40 * 3370189 * 2
def baseEnd_3370189 : Nat := 1153684568997079902492193

theorem tailTrace_3370189 : CollatzResearch.WordTrace tailWord_3370189 prefixEnd_3370189 1153684568997079902492193 := by
  unfold tailWord_3370189
  simp only [CollatzResearch.WordTrace]
  refine ⟨122920891187388310301849621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81947260791592206867899747 122920891187388310301849621)
  ·
    refine ⟨5761916774408827045399201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 122920891187388310301849621 5761916774408827045399201)
    ·
      refine ⟨4321437580806620284049401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5761916774408827045399201 4321437580806620284049401)
      ·
        refine ⟨3241078185604965213037051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4321437580806620284049401 3241078185604965213037051)
        ·
          refine ⟨4861617278407447819555577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3241078185604965213037051 4861617278407447819555577)
          ·
            refine ⟨3646212958805585864666683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4861617278407447819555577 3646212958805585864666683)
            ·
              refine ⟨5469319438208378797000025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3646212958805585864666683 5469319438208378797000025)
              ·
                refine ⟨4101989578656284097750019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5469319438208378797000025 4101989578656284097750019)
                ·
                  refine ⟨6152984367984426146625029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4101989578656284097750019 6152984367984426146625029)
                  ·
                    refine ⟨1153684568997079902492193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6152984367984426146625029 1153684568997079902492193)
                    ·
                      rfl

theorem cell22_3370189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_3370189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3370189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3370189 prefixEnd_3370189 := by exact prefixLift 3370189
  have htrace : WordTrace (prefixWord ++ tailWord_3370189) baseStart_3370189 baseEnd_3370189 := by
    simpa [prefixWord, tailWord_3370189, baseEnd_3370189] using wordTrace_append hprefix tailTrace_3370189
  have hstable : (prefixWord ++ tailWord_3370189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370189).length < 2 ^ (prefixWord ++ tailWord_3370189).sum := by decide
  have hdescent : baseEnd_3370189 < baseStart_3370189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370241 : List Nat := [1, 2, 4, 1, 1, 3, 1, 1, 1, 7]
def baseStart_3370241 : Nat := 118140960795 + 3370241 * 2 ^ 59
def prefixEnd_3370241 : Nat := 4983230072969 + 3 ^ 40 * 3370241 * 2
def baseEnd_3370241 : Nat := 1153702369659769100192033

theorem tailTrace_3370241 : CollatzResearch.WordTrace tailWord_3370241 prefixEnd_3370241 1153702369659769100192033 := by
  unfold tailWord_3370241
  simp only [CollatzResearch.WordTrace]
  refine ⟨122922787783199923182742577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81948525188799948788495051 122922787783199923182742577)
  ·
    refine ⟨92192090837399942387056933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122922787783199923182742577 92192090837399942387056933)
    ·
      refine ⟨17286017032012489197573175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92192090837399942387056933 17286017032012489197573175)
      ·
        refine ⟨25929025548018733796359763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17286017032012489197573175 25929025548018733796359763)
        ·
          refine ⟨38893538322028100694539645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25929025548018733796359763 38893538322028100694539645)
          ·
            refine ⟨14585076870760537760452367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38893538322028100694539645 14585076870760537760452367)
            ·
              refine ⟨21877615306140806640678551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14585076870760537760452367 21877615306140806640678551)
              ·
                refine ⟨32816422959211209961017827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21877615306140806640678551 32816422959211209961017827)
                ·
                  refine ⟨49224634438816814941526741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32816422959211209961017827 49224634438816814941526741)
                  ·
                    refine ⟨1153702369659769100192033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49224634438816814941526741 1153702369659769100192033)
                    ·
                      rfl

theorem cell22_3370241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_3370241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3370241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3370241 prefixEnd_3370241 := by exact prefixLift 3370241
  have htrace : WordTrace (prefixWord ++ tailWord_3370241) baseStart_3370241 baseEnd_3370241 := by
    simpa [prefixWord, tailWord_3370241, baseEnd_3370241] using wordTrace_append hprefix tailTrace_3370241
  have hstable : (prefixWord ++ tailWord_3370241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370241).length < 2 ^ (prefixWord ++ tailWord_3370241).sum := by decide
  have hdescent : baseEnd_3370241 < baseStart_3370241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370288 : List Nat := [2, 1, 1, 1, 2, 2, 3, 6, 4]
def baseStart_3370288 : Nat := 118140960795 + 3370288 * 2 ^ 59
def prefixEnd_3370288 : Nat := 4983230072969 + 3 ^ 40 * 3370288 * 2
def baseEnd_3370288 : Nat := 384572819573425548088963

theorem tailTrace_3370288 : CollatzResearch.WordTrace tailWord_3370288 prefixEnd_3370288 384572819573425548088963 := by
  unfold tailWord_3370288
  simp only [CollatzResearch.WordTrace]
  refine ⟨61462251007014825104851759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81949668009353100139802345 61462251007014825104851759)
  ·
    refine ⟨92193376510522237657277639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61462251007014825104851759 92193376510522237657277639)
    ·
      refine ⟨138290064765783356485916459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92193376510522237657277639 138290064765783356485916459)
      ·
        refine ⟨207435097148675034728874689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138290064765783356485916459 207435097148675034728874689)
        ·
          refine ⟨155576322861506276046656017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207435097148675034728874689 155576322861506276046656017)
          ·
            refine ⟨116682242146129707034992013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155576322861506276046656017 116682242146129707034992013)
            ·
              refine ⟨43755840804798640138122005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116682242146129707034992013 43755840804798640138122005)
              ·
                refine ⟨2051055037724936256474469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43755840804798640138122005 2051055037724936256474469)
                ·
                  refine ⟨384572819573425548088963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2051055037724936256474469 384572819573425548088963)
                  ·
                    rfl

theorem cell22_3370288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 6, 4].length) (baseStart_3370288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3370288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3370288 prefixEnd_3370288 := by exact prefixLift 3370288
  have htrace : WordTrace (prefixWord ++ tailWord_3370288) baseStart_3370288 baseEnd_3370288 := by
    simpa [prefixWord, tailWord_3370288, baseEnd_3370288] using wordTrace_append hprefix tailTrace_3370288
  have hstable : (prefixWord ++ tailWord_3370288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370288).length < 2 ^ (prefixWord ++ tailWord_3370288).sum := by decide
  have hdescent : baseEnd_3370288 < baseStart_3370288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370294 : List Nat := [5, 1, 2, 3, 1, 1, 3, 1, 5]
def baseStart_3370294 : Nat := 118140960795 + 3370294 * 2 ^ 59
def prefixEnd_3370294 : Nat := 4983230072969 + 3 ^ 40 * 3370294 * 2
def baseEnd_3370294 : Nat := 384573504214298209538957

theorem tailTrace_3370294 : CollatzResearch.WordTrace tailWord_3370294 prefixEnd_3370294 384573504214298209538957 := by
  unfold tailWord_3370294
  simp only [CollatzResearch.WordTrace]
  refine ⟨7682795053250494577151371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81949813901338608822947957 7682795053250494577151371)
  ·
    refine ⟨11524192579875741865727057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7682795053250494577151371 11524192579875741865727057)
    ·
      refine ⟨8643144434906806399295293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11524192579875741865727057 8643144434906806399295293)
      ·
        refine ⟨3241179163090052399735735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8643144434906806399295293 3241179163090052399735735)
        ·
          refine ⟨4861768744635078599603603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3241179163090052399735735 4861768744635078599603603)
          ·
            refine ⟨7292653116952617899405405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4861768744635078599603603 7292653116952617899405405)
            ·
              refine ⟨2734744918857231712277027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7292653116952617899405405 2734744918857231712277027)
              ·
                refine ⟨4102117378285847568415541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2734744918857231712277027 4102117378285847568415541)
                ·
                  refine ⟨384573504214298209538957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4102117378285847568415541 384573504214298209538957)
                  ·
                    rfl

theorem cell22_3370294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_3370294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3370294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3370294 prefixEnd_3370294 := by exact prefixLift 3370294
  have htrace : WordTrace (prefixWord ++ tailWord_3370294) baseStart_3370294 baseEnd_3370294 := by
    simpa [prefixWord, tailWord_3370294, baseEnd_3370294] using wordTrace_append hprefix tailTrace_3370294
  have hstable : (prefixWord ++ tailWord_3370294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370294).length < 2 ^ (prefixWord ++ tailWord_3370294).sum := by decide
  have hdescent : baseEnd_3370294 < baseStart_3370294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370303 : List Nat := [1, 1, 2, 2, 4, 2, 3, 1, 1, 5]
def baseStart_3370303 : Nat := 118140960795 + 3370303 * 2 ^ 59
def prefixEnd_3370303 : Nat := 4983230072969 + 3 ^ 40 * 3370303 * 2
def baseEnd_3370303 : Nat := 1153723593526821605141843

theorem tailTrace_3370303 : CollatzResearch.WordTrace tailWord_3370303 prefixEnd_3370303 1153723593526821605141843 := by
  unfold tailWord_3370303
  simp only [CollatzResearch.WordTrace]
  refine ⟨122925049108975307771499563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81950032739316871847666375 122925049108975307771499563)
  ·
    refine ⟨184387573663462961657249345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122925049108975307771499563 184387573663462961657249345)
    ·
      refine ⟨138290680247597221242937009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184387573663462961657249345 138290680247597221242937009)
      ·
        refine ⟨103718010185697915932202757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138290680247597221242937009 103718010185697915932202757)
        ·
          refine ⟨19447126909818359237288017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103718010185697915932202757 19447126909818359237288017)
          ·
            refine ⟨14585345182363769427966013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19447126909818359237288017 14585345182363769427966013)
            ·
              refine ⟨5469504443386413535487255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14585345182363769427966013 5469504443386413535487255)
              ·
                refine ⟨8204256665079620303230883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5469504443386413535487255 8204256665079620303230883)
                ·
                  refine ⟨12306384997619430454846325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8204256665079620303230883 12306384997619430454846325)
                  ·
                    refine ⟨1153723593526821605141843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12306384997619430454846325 1153723593526821605141843)
                    ·
                      rfl

theorem cell22_3370303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 1, 1, 5].length) (baseStart_3370303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3370303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3370303 prefixEnd_3370303 := by exact prefixLift 3370303
  have htrace : WordTrace (prefixWord ++ tailWord_3370303) baseStart_3370303 baseEnd_3370303 := by
    simpa [prefixWord, tailWord_3370303, baseEnd_3370303] using wordTrace_append hprefix tailTrace_3370303
  have hstable : (prefixWord ++ tailWord_3370303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370303).length < 2 ^ (prefixWord ++ tailWord_3370303).sum := by decide
  have hdescent : baseEnd_3370303 < baseStart_3370303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370318 : List Nat := [4, 1, 1, 1, 1, 1, 4, 3, 2, 4]
def baseStart_3370318 : Nat := 118140960795 + 3370318 * 2 ^ 59
def prefixEnd_3370318 : Nat := 4983230072969 + 3 ^ 40 * 3370318 * 2
def baseEnd_3370318 : Nat := 1153728728333366566016797

theorem tailTrace_3370318 : CollatzResearch.WordTrace tailWord_3370318 prefixEnd_3370318 1153728728333366566016797 := by
  unfold tailWord_3370318
  simp only [CollatzResearch.WordTrace]
  refine ⟨15365699525490120666661951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81950397469280643555530405 15365699525490120666661951)
  ·
    refine ⟨23048549288235180999992927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15365699525490120666661951 23048549288235180999992927)
    ·
      refine ⟨34572823932352771499989391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23048549288235180999992927 34572823932352771499989391)
      ·
        refine ⟨51859235898529157249984087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34572823932352771499989391 51859235898529157249984087)
        ·
          refine ⟨77788853847793735874976131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51859235898529157249984087 77788853847793735874976131)
          ·
            refine ⟨116683280771690603812464197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77788853847793735874976131 116683280771690603812464197)
            ·
              refine ⟨21878115144691988214837037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116683280771690603812464197 21878115144691988214837037)
              ·
                refine ⟨8204293179259495580563889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21878115144691988214837037 8204293179259495580563889)
                ·
                  refine ⟨6153219884444621685422917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8204293179259495580563889 6153219884444621685422917)
                  ·
                    refine ⟨1153728728333366566016797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6153219884444621685422917 1153728728333366566016797)
                    ·
                      rfl

theorem cell22_3370318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_3370318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3370318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3370318 prefixEnd_3370318 := by exact prefixLift 3370318
  have htrace : WordTrace (prefixWord ++ tailWord_3370318) baseStart_3370318 baseEnd_3370318 := by
    simpa [prefixWord, tailWord_3370318, baseEnd_3370318] using wordTrace_append hprefix tailTrace_3370318
  have hstable : (prefixWord ++ tailWord_3370318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370318).length < 2 ^ (prefixWord ++ tailWord_3370318).sum := by decide
  have hdescent : baseEnd_3370318 < baseStart_3370318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370399 : List Nat := [1, 1, 2, 5, 1, 2, 4, 2, 1, 3]
def baseStart_3370399 : Nat := 118140960795 + 3370399 * 2 ^ 59
def prefixEnd_3370399 : Nat := 4983230072969 + 3 ^ 40 * 3370399 * 2
def baseEnd_3370399 : Nat := 1153756456288709354741549

theorem tailTrace_3370399 : CollatzResearch.WordTrace tailWord_3370399 prefixEnd_3370399 1153756456288709354741549 := by
  unfold tailWord_3370399
  simp only [CollatzResearch.WordTrace]
  refine ⟨122928550516627516166994251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81952367011085010777996167 122928550516627516166994251)
  ·
    refine ⟨184392825774941274250491377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122928550516627516166994251 184392825774941274250491377)
    ·
      refine ⟨138294619331205955687868533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184392825774941274250491377 138294619331205955687868533)
      ·
        refine ⟨12965120562300558345737675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 138294619331205955687868533 12965120562300558345737675)
        ·
          refine ⟨19447680843450837518606513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12965120562300558345737675 19447680843450837518606513)
          ·
            refine ⟨14585760632588128138954885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19447680843450837518606513 14585760632588128138954885)
            ·
              refine ⟨2734830118610274026054041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14585760632588128138954885 2734830118610274026054041)
              ·
                refine ⟨2051122588957705519540531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2734830118610274026054041 2051122588957705519540531)
                ·
                  refine ⟨3076683883436558279310797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2051122588957705519540531 3076683883436558279310797)
                  ·
                    refine ⟨1153756456288709354741549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3076683883436558279310797 1153756456288709354741549)
                    ·
                      rfl

theorem cell22_3370399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4, 2, 1, 3].length) (baseStart_3370399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3370399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3370399 prefixEnd_3370399 := by exact prefixLift 3370399
  have htrace : WordTrace (prefixWord ++ tailWord_3370399) baseStart_3370399 baseEnd_3370399 := by
    simpa [prefixWord, tailWord_3370399, baseEnd_3370399] using wordTrace_append hprefix tailTrace_3370399
  have hstable : (prefixWord ++ tailWord_3370399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370399).length < 2 ^ (prefixWord ++ tailWord_3370399).sum := by decide
  have hdescent : baseEnd_3370399 < baseStart_3370399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370423 : List Nat := [1, 1, 3, 1, 3, 2, 3, 2, 6]
def baseStart_3370423 : Nat := 118140960795 + 3370423 * 2 ^ 59
def prefixEnd_3370423 : Nat := 4983230072969 + 3 ^ 40 * 3370423 * 2
def baseEnd_3370423 : Nat := 384588223993060430713825

theorem tailTrace_3370423 : CollatzResearch.WordTrace tailWord_3370423 prefixEnd_3370423 384588223993060430713825 := by
  unfold tailWord_3370423
  simp only [CollatzResearch.WordTrace]
  refine ⟨122929425868540568265867923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81952950579027045510578615 122929425868540568265867923)
  ·
    refine ⟨184394138802810852398801885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122929425868540568265867923 184394138802810852398801885)
    ·
      refine ⟨69147802051054069649550707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184394138802810852398801885 69147802051054069649550707)
      ·
        refine ⟨103721703076581104474326061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69147802051054069649550707 103721703076581104474326061)
        ·
          refine ⟨38895638653717914177872273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103721703076581104474326061 38895638653717914177872273)
          ·
            refine ⟨29171728990288435633404205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38895638653717914177872273 29171728990288435633404205)
            ·
              refine ⟨10939398371358163362526577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29171728990288435633404205 10939398371358163362526577)
              ·
                refine ⟨8204548778518622521894933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10939398371358163362526577 8204548778518622521894933)
                ·
                  refine ⟨384588223993060430713825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8204548778518622521894933 384588223993060430713825)
                  ·
                    rfl

theorem cell22_3370423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 6].length) (baseStart_3370423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3370423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3370423 prefixEnd_3370423 := by exact prefixLift 3370423
  have htrace : WordTrace (prefixWord ++ tailWord_3370423) baseStart_3370423 baseEnd_3370423 := by
    simpa [prefixWord, tailWord_3370423, baseEnd_3370423] using wordTrace_append hprefix tailTrace_3370423
  have hstable : (prefixWord ++ tailWord_3370423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370423).length < 2 ^ (prefixWord ++ tailWord_3370423).sum := by decide
  have hdescent : baseEnd_3370423 < baseStart_3370423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370442 : List Nat := [3, 1, 2, 1, 2, 3, 4, 1, 1, 4]
def baseStart_3370442 : Nat := 118140960795 + 3370442 * 2 ^ 59
def prefixEnd_3370442 : Nat := 4983230072969 + 3 ^ 40 * 3370442 * 2
def baseEnd_3370442 : Nat := 1153771176067471575916417

theorem tailTrace_3370442 : CollatzResearch.WordTrace tailWord_3370442 prefixEnd_3370442 1153771176067471575916417 := by
  unfold tailWord_3370442
  simp only [CollatzResearch.WordTrace]
  refine ⟨30732529713867933627702395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81953412570314489673873053 30732529713867933627702395)
  ·
    refine ⟨46098794570801900441553593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30732529713867933627702395 46098794570801900441553593)
    ·
      refine ⟨34574095928101425331165195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46098794570801900441553593 34574095928101425331165195)
      ·
        refine ⟨51861143892152137996747793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34574095928101425331165195 51861143892152137996747793)
        ·
          refine ⟨38895857919114103497560845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51861143892152137996747793 38895857919114103497560845)
          ·
            refine ⟨14585946719667788811585317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38895857919114103497560845 14585946719667788811585317)
            ·
              refine ⟨2734865009937710402172247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14585946719667788811585317 2734865009937710402172247)
              ·
                refine ⟨4102297514906565603258371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2734865009937710402172247 4102297514906565603258371)
                ·
                  refine ⟨6153446272359848404887557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4102297514906565603258371 6153446272359848404887557)
                  ·
                    refine ⟨1153771176067471575916417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6153446272359848404887557 1153771176067471575916417)
                    ·
                      rfl

theorem cell22_3370442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4, 1, 1, 4].length) (baseStart_3370442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3370442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3370442 prefixEnd_3370442 := by exact prefixLift 3370442
  have htrace : WordTrace (prefixWord ++ tailWord_3370442) baseStart_3370442 baseEnd_3370442 := by
    simpa [prefixWord, tailWord_3370442, baseEnd_3370442] using wordTrace_append hprefix tailTrace_3370442
  have hstable : (prefixWord ++ tailWord_3370442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370442).length < 2 ^ (prefixWord ++ tailWord_3370442).sum := by decide
  have hdescent : baseEnd_3370442 < baseStart_3370442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370513 : List Nat := [1, 2, 2, 1, 1, 2, 3, 3, 7]
def baseStart_3370513 : Nat := 118140960795 + 3370513 * 2 ^ 59
def prefixEnd_3370513 : Nat := 4983230072969 + 3 ^ 40 * 3370513 * 2
def baseEnd_3370513 : Nat := 384598493606150352463733

theorem tailTrace_3370513 : CollatzResearch.WordTrace tailWord_3370513 prefixEnd_3370513 384598493606150352463733 := by
  unfold tailWord_3370513
  simp only [CollatzResearch.WordTrace]
  refine ⟨122932708438214513636644193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81955138958809675757762795 122932708438214513636644193)
  ·
    refine ⟨92199531328660885227483145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122932708438214513636644193 92199531328660885227483145)
    ·
      refine ⟨69149648496495663920612359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92199531328660885227483145 69149648496495663920612359)
      ·
        refine ⟨103724472744743495880918539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69149648496495663920612359 103724472744743495880918539)
        ·
          refine ⟨155586709117115243821377809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103724472744743495880918539 155586709117115243821377809)
          ·
            refine ⟨116690031837836432866033357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155586709117115243821377809 116690031837836432866033357)
            ·
              refine ⟨43758761939188662324762509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116690031837836432866033357 43758761939188662324762509)
              ·
                refine ⟨16409535727195748371785941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43758761939188662324762509 16409535727195748371785941)
                ·
                  refine ⟨384598493606150352463733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16409535727195748371785941 384598493606150352463733)
                  ·
                    rfl

theorem cell22_3370513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 7].length) (baseStart_3370513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3370513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3370513 prefixEnd_3370513 := by exact prefixLift 3370513
  have htrace : WordTrace (prefixWord ++ tailWord_3370513) baseStart_3370513 baseEnd_3370513 := by
    simpa [prefixWord, tailWord_3370513, baseEnd_3370513] using wordTrace_append hprefix tailTrace_3370513
  have hstable : (prefixWord ++ tailWord_3370513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370513).length < 2 ^ (prefixWord ++ tailWord_3370513).sum := by decide
  have hdescent : baseEnd_3370513 < baseStart_3370513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370517 : List Nat := [1, 3, 2, 1, 3, 2, 3, 1, 3, 3]
def baseStart_3370517 : Nat := 118140960795 + 3370517 * 2 ^ 59
def prefixEnd_3370517 : Nat := 4983230072969 + 3 ^ 40 * 3370517 * 2
def baseEnd_3370517 : Nat := 1153796850100196380291187

theorem tailTrace_3370517 : CollatzResearch.WordTrace tailWord_3370517 prefixEnd_3370517 1153796850100196380291187 := by
  unfold tailWord_3370517
  simp only [CollatzResearch.WordTrace]
  refine ⟨122932854330200022319789805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81955236220133348213193203 122932854330200022319789805)
  ·
    refine ⟨46099820373825008369921177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122932854330200022319789805 46099820373825008369921177)
    ·
      refine ⟨34574865280368756277440883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46099820373825008369921177 34574865280368756277440883)
      ·
        refine ⟨51862297920553134416161325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34574865280368756277440883 51862297920553134416161325)
        ·
          refine ⟨19448361720207425406060497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51862297920553134416161325 19448361720207425406060497)
          ·
            refine ⟨14586271290155569054545373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19448361720207425406060497 14586271290155569054545373)
            ·
              refine ⟨5469851733808338395454515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14586271290155569054545373 5469851733808338395454515)
              ·
                refine ⟨8204777600712507593181773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5469851733808338395454515 8204777600712507593181773)
                ·
                  refine ⟨3076791600267190347443165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8204777600712507593181773 3076791600267190347443165)
                  ·
                    refine ⟨1153796850100196380291187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3076791600267190347443165 1153796850100196380291187)
                    ·
                      rfl

theorem cell22_3370517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 1, 3, 3].length) (baseStart_3370517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3370517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3370517 prefixEnd_3370517 := by exact prefixLift 3370517
  have htrace : WordTrace (prefixWord ++ tailWord_3370517) baseStart_3370517 baseEnd_3370517 := by
    simpa [prefixWord, tailWord_3370517, baseEnd_3370517] using wordTrace_append hprefix tailTrace_3370517
  have hstable : (prefixWord ++ tailWord_3370517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370517).length < 2 ^ (prefixWord ++ tailWord_3370517).sum := by decide
  have hdescent : baseEnd_3370517 < baseStart_3370517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370654 : List Nat := [4, 3, 1, 1, 1, 2, 4, 6]
def baseStart_3370654 : Nat := 118140960795 + 3370654 * 2 ^ 59
def prefixEnd_3370654 : Nat := 4983230072969 + 3 ^ 40 * 3370654 * 2
def baseEnd_3370654 : Nat := 128204860888885965512863

theorem tailTrace_3370654 : CollatzResearch.WordTrace tailWord_3370654 prefixEnd_3370654 128204860888885965512863 := by
  unfold tailWord_3370654
  simp only [CollatzResearch.WordTrace]
  refine ⟨15367231391337961839690877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81958567420469129811684677 15367231391337961839690877)
  ·
    refine ⟨5762711771751735689884079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15367231391337961839690877 5762711771751735689884079)
    ·
      refine ⟨8644067657627603534826119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5762711771751735689884079 8644067657627603534826119)
      ·
        refine ⟨12966101486441405302239179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8644067657627603534826119 12966101486441405302239179)
        ·
          refine ⟨19449152229662107953358769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12966101486441405302239179 19449152229662107953358769)
          ·
            refine ⟨14586864172246580965019077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19449152229662107953358769 14586864172246580965019077)
            ·
              refine ⟨2735037032296233930941077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14586864172246580965019077 2735037032296233930941077)
              ·
                refine ⟨128204860888885965512863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2735037032296233930941077 128204860888885965512863)
                ·
                  rfl

theorem cell22_3370654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4, 6].length) (baseStart_3370654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3370654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3370654 prefixEnd_3370654 := by exact prefixLift 3370654
  have htrace : WordTrace (prefixWord ++ tailWord_3370654) baseStart_3370654 baseEnd_3370654 := by
    simpa [prefixWord, tailWord_3370654, baseEnd_3370654] using wordTrace_append hprefix tailTrace_3370654
  have hstable : (prefixWord ++ tailWord_3370654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370654).length < 2 ^ (prefixWord ++ tailWord_3370654).sum := by decide
  have hdescent : baseEnd_3370654 < baseStart_3370654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370680 : List Nat := [2, 1, 2, 1, 2, 1, 1, 3, 4, 5]
def baseStart_3370680 : Nat := 118140960795 + 3370680 * 2 ^ 59
def prefixEnd_3370680 : Nat := 4983230072969 + 3 ^ 40 * 3370680 * 2
def baseEnd_3370680 : Nat := 1153852648331318288465687

theorem tailTrace_3370680 : CollatzResearch.WordTrace tailWord_3370680 prefixEnd_3370680 1153852648331318288465687 := by
  unfold tailWord_3370680
  simp only [CollatzResearch.WordTrace]
  refine ⟨61469399714304750578986747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81959199619073000771982329 61469399714304750578986747)
  ·
    refine ⟨92204099571457125868480121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61469399714304750578986747 92204099571457125868480121)
    ·
      refine ⟨69153074678592844401360091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92204099571457125868480121 69153074678592844401360091)
      ·
        refine ⟨103729612017889266602040137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69153074678592844401360091 103729612017889266602040137)
        ·
          refine ⟨77797209013416949951530103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103729612017889266602040137 77797209013416949951530103)
          ·
            refine ⟨116695813520125424927295155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77797209013416949951530103 116695813520125424927295155)
            ·
              refine ⟨175043720280188137390942733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116695813520125424927295155 175043720280188137390942733)
              ·
                refine ⟨65641395105070551521603525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 175043720280188137390942733 65641395105070551521603525)
                ·
                  refine ⟨12307761582200728410300661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65641395105070551521603525 12307761582200728410300661)
                  ·
                    refine ⟨1153852648331318288465687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12307761582200728410300661 1153852648331318288465687)
                    ·
                      rfl

theorem cell22_3370680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 4, 5].length) (baseStart_3370680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3370680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3370680 prefixEnd_3370680 := by exact prefixLift 3370680
  have htrace : WordTrace (prefixWord ++ tailWord_3370680) baseStart_3370680 baseEnd_3370680 := by
    simpa [prefixWord, tailWord_3370680, baseEnd_3370680] using wordTrace_append hprefix tailTrace_3370680
  have hstable : (prefixWord ++ tailWord_3370680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370680).length < 2 ^ (prefixWord ++ tailWord_3370680).sum := by decide
  have hdescent : baseEnd_3370680 < baseStart_3370680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370686 : List Nat := [4, 2, 1, 1, 2, 4, 1, 1, 3, 3]
def baseStart_3370686 : Nat := 118140960795 + 3370686 * 2 ^ 59
def prefixEnd_3370686 : Nat := 4983230072969 + 3 ^ 40 * 3370686 * 2
def baseEnd_3370686 : Nat := 1153854702253936272815669

theorem tailTrace_3370686 : CollatzResearch.WordTrace tailWord_3370686 prefixEnd_3370686 1153854702253936272815669 := by
  unfold tailWord_3370686
  simp only [CollatzResearch.WordTrace]
  refine ⟨15367377283323470522836489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81959345511058509455127941 15367377283323470522836489)
  ·
    refine ⟨11525532962492602892127367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15367377283323470522836489 11525532962492602892127367)
    ·
      refine ⟨17288299443738904338191051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11525532962492602892127367 17288299443738904338191051)
      ·
        refine ⟨25932449165608356507286577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17288299443738904338191051 25932449165608356507286577)
        ·
          refine ⟨19449336874206267380464933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25932449165608356507286577 19449336874206267380464933)
          ·
            refine ⟨3646750663913675133837175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19449336874206267380464933 3646750663913675133837175)
            ·
              refine ⟨5470125995870512700755763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3646750663913675133837175 5470125995870512700755763)
              ·
                refine ⟨8205188993805769051133645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5470125995870512700755763 8205188993805769051133645)
                ·
                  refine ⟨3076945872677163394175117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8205188993805769051133645 3076945872677163394175117)
                  ·
                    refine ⟨1153854702253936272815669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3076945872677163394175117 1153854702253936272815669)
                    ·
                      rfl

theorem cell22_3370686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_3370686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3370686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3370686 prefixEnd_3370686 := by exact prefixLift 3370686
  have htrace : WordTrace (prefixWord ++ tailWord_3370686) baseStart_3370686 baseEnd_3370686 := by
    simpa [prefixWord, tailWord_3370686, baseEnd_3370686] using wordTrace_append hprefix tailTrace_3370686
  have hstable : (prefixWord ++ tailWord_3370686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370686).length < 2 ^ (prefixWord ++ tailWord_3370686).sum := by decide
  have hdescent : baseEnd_3370686 < baseStart_3370686 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370712 : List Nat := [2, 1, 2, 2, 3, 1, 3, 1, 3, 4]
def baseStart_3370712 : Nat := 118140960795 + 3370712 * 2 ^ 59
def prefixEnd_3370712 : Nat := 4983230072969 + 3 ^ 40 * 3370712 * 2
def baseEnd_3370712 : Nat := 1153863602585280871665589

theorem tailTrace_3370712 : CollatzResearch.WordTrace tailWord_3370712 prefixEnd_3370712 1153863602585280871665589 := by
  unfold tailWord_3370712
  simp only [CollatzResearch.WordTrace]
  refine ⟨61469983282246785311569195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81959977709662380415425593 61469983282246785311569195)
  ·
    refine ⟨92204974923370177967353793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61469983282246785311569195 92204974923370177967353793)
    ·
      refine ⟨69153731192527633475515345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92204974923370177967353793 69153731192527633475515345)
      ·
        refine ⟨51865298394395725106636509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69153731192527633475515345 51865298394395725106636509)
        ·
          refine ⟨19449486897898396914988691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51865298394395725106636509 19449486897898396914988691)
          ·
            refine ⟨29174230346847595372483037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19449486897898396914988691 29174230346847595372483037)
            ·
              refine ⟨10940336380067848264681139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29174230346847595372483037 10940336380067848264681139)
              ·
                refine ⟨16410504570101772397021709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10940336380067848264681139 16410504570101772397021709)
                ·
                  refine ⟨6153939213788164648883141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16410504570101772397021709 6153939213788164648883141)
                  ·
                    refine ⟨1153863602585280871665589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6153939213788164648883141 1153863602585280871665589)
                    ·
                      rfl

theorem cell22_3370712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 3, 4].length) (baseStart_3370712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3370712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3370712 prefixEnd_3370712 := by exact prefixLift 3370712
  have htrace : WordTrace (prefixWord ++ tailWord_3370712) baseStart_3370712 baseEnd_3370712 := by
    simpa [prefixWord, tailWord_3370712, baseEnd_3370712] using wordTrace_append hprefix tailTrace_3370712
  have hstable : (prefixWord ++ tailWord_3370712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370712).length < 2 ^ (prefixWord ++ tailWord_3370712).sum := by decide
  have hdescent : baseEnd_3370712 < baseStart_3370712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370913 : List Nat := [1, 2, 3, 4, 2, 1, 1, 4, 4]
def baseStart_3370913 : Nat := 118140960795 + 3370913 * 2 ^ 59
def prefixEnd_3370913 : Nat := 4983230072969 + 3 ^ 40 * 3370913 * 2
def baseEnd_3370913 : Nat := 384644136330994449129991

theorem tailTrace_3370913 : CollatzResearch.WordTrace tailWord_3370913 prefixEnd_3370913 384644136330994449129991 := by
  unfold tailWord_3370913
  simp only [CollatzResearch.WordTrace]
  refine ⟨122947297636765381951205393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81964865091176921300803595 122947297636765381951205393)
  ·
    refine ⟨92210473227574036463404045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122947297636765381951205393 92210473227574036463404045)
    ·
      refine ⟨34578927460340263673776517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92210473227574036463404045 34578927460340263673776517)
      ·
        refine ⟨6483548898813799438833097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34578927460340263673776517 6483548898813799438833097)
        ·
          refine ⟨4862661674110349579124823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6483548898813799438833097 4862661674110349579124823)
          ·
            refine ⟨7293992511165524368687235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4862661674110349579124823 7293992511165524368687235)
            ·
              refine ⟨10940988766748286553030853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7293992511165524368687235 10940988766748286553030853)
              ·
                refine ⟨2051435393765303728693285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10940988766748286553030853 2051435393765303728693285)
                ·
                  refine ⟨384644136330994449129991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2051435393765303728693285 384644136330994449129991)
                  ·
                    rfl

theorem cell22_3370913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 4, 4].length) (baseStart_3370913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3370913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3370913 prefixEnd_3370913 := by exact prefixLift 3370913
  have htrace : WordTrace (prefixWord ++ tailWord_3370913) baseStart_3370913 baseEnd_3370913 := by
    simpa [prefixWord, tailWord_3370913, baseEnd_3370913] using wordTrace_append hprefix tailTrace_3370913
  have hstable : (prefixWord ++ tailWord_3370913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370913).length < 2 ^ (prefixWord ++ tailWord_3370913).sum := by decide
  have hdescent : baseEnd_3370913 < baseStart_3370913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370939 : List Nat := [1, 1, 1, 1, 1, 2, 2, 5, 5, 3]
def baseStart_3370939 : Nat := 118140960795 + 3370939 * 2 ^ 59
def prefixEnd_3370939 : Nat := 4983230072969 + 3 ^ 40 * 3370939 * 2
def baseEnd_3370939 : Nat := 1153941309324327946239893

theorem tailTrace_3370939 : CollatzResearch.WordTrace tailWord_3370939 prefixEnd_3370939 1153941309324327946239893 := by
  unfold tailWord_3370939
  simp only [CollatzResearch.WordTrace]
  refine ⟨122948245934671188391651871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81965497289780792261101247 122948245934671188391651871)
  ·
    refine ⟨184422368902006782587477807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122948245934671188391651871 184422368902006782587477807)
    ·
      refine ⟨276633553353010173881216711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184422368902006782587477807 276633553353010173881216711)
      ·
        refine ⟨414950330029515260821825067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276633553353010173881216711 414950330029515260821825067)
        ·
          refine ⟨622425495044272891232737601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414950330029515260821825067 622425495044272891232737601)
          ·
            refine ⟨466819121283204668424553201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 622425495044272891232737601 466819121283204668424553201)
            ·
              refine ⟨350114340962403501318414901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 466819121283204668424553201 350114340962403501318414901)
              ·
                refine ⟨32823219465225328248601397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 350114340962403501318414901 32823219465225328248601397)
                ·
                  refine ⟨3077176824864874523306381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32823219465225328248601397 3077176824864874523306381)
                  ·
                    refine ⟨1153941309324327946239893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3077176824864874523306381 1153941309324327946239893)
                    ·
                      rfl

theorem cell22_3370939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 5, 3].length) (baseStart_3370939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3370939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3370939 prefixEnd_3370939 := by exact prefixLift 3370939
  have htrace : WordTrace (prefixWord ++ tailWord_3370939) baseStart_3370939 baseEnd_3370939 := by
    simpa [prefixWord, tailWord_3370939, baseEnd_3370939] using wordTrace_append hprefix tailTrace_3370939
  have hstable : (prefixWord ++ tailWord_3370939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370939).length < 2 ^ (prefixWord ++ tailWord_3370939).sum := by decide
  have hdescent : baseEnd_3370939 < baseStart_3370939 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370941 : List Nat := [1, 4, 1, 2, 3, 2, 3, 6]
def baseStart_3370941 : Nat := 118140960795 + 3370941 * 2 ^ 59
def prefixEnd_3370941 : Nat := 4983230072969 + 3 ^ 40 * 3370941 * 2
def baseEnd_3370941 : Nat := 128215777107244511965543

theorem tailTrace_3370941 : CollatzResearch.WordTrace tailWord_3370941 prefixEnd_3370941 128215777107244511965543 := by
  unfold tailWord_3370941
  simp only [CollatzResearch.WordTrace]
  refine ⟨122948318880663942733224677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81965545920442628488816451 122948318880663942733224677)
  ·
    refine ⟨23052809790124489262479627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122948318880663942733224677 23052809790124489262479627)
    ·
      refine ⟨34579214685186733893719441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23052809790124489262479627 34579214685186733893719441)
      ·
        refine ⟨25934411013890050420289581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34579214685186733893719441 25934411013890050420289581)
        ·
          refine ⟨9725404130208768907608593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25934411013890050420289581 9725404130208768907608593)
          ·
            refine ⟨7294053097656576680706445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9725404130208768907608593 7294053097656576680706445)
            ·
              refine ⟨2735269911621216255264917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7294053097656576680706445 2735269911621216255264917)
              ·
                refine ⟨128215777107244511965543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2735269911621216255264917 128215777107244511965543)
                ·
                  rfl

theorem cell22_3370941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3, 6].length) (baseStart_3370941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3370941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3370941 prefixEnd_3370941 := by exact prefixLift 3370941
  have htrace : WordTrace (prefixWord ++ tailWord_3370941) baseStart_3370941 baseEnd_3370941 := by
    simpa [prefixWord, tailWord_3370941, baseEnd_3370941] using wordTrace_append hprefix tailTrace_3370941
  have hstable : (prefixWord ++ tailWord_3370941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370941).length < 2 ^ (prefixWord ++ tailWord_3370941).sum := by decide
  have hdescent : baseEnd_3370941 < baseStart_3370941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370962 : List Nat := [3, 2, 2, 3, 3, 1, 1, 2, 2, 3]
def baseStart_3370962 : Nat := 118140960795 + 3370962 * 2 ^ 59
def prefixEnd_3370962 : Nat := 4983230072969 + 3 ^ 40 * 3370962 * 2
def baseEnd_3370962 : Nat := 1153949182694363552914823

theorem tailTrace_3370962 : CollatzResearch.WordTrace tailWord_3370962 prefixEnd_3370962 1153949182694363552914823 := by
  unfold tailWord_3370962
  simp only [CollatzResearch.WordTrace]
  refine ⟨30737271203396965829934785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81966056542391908879826093 30737271203396965829934785)
  ·
    refine ⟨23052953402547724372451089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30737271203396965829934785 23052953402547724372451089)
    ·
      refine ⟨17289715051910793279338317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23052953402547724372451089 17289715051910793279338317)
      ·
        refine ⟨6483643144466547479751869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17289715051910793279338317 6483643144466547479751869)
        ·
          refine ⟨2431366179174955304906951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6483643144466547479751869 2431366179174955304906951)
          ·
            refine ⟨3647049268762432957360427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2431366179174955304906951 3647049268762432957360427)
            ·
              refine ⟨5470573903143649436040641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3647049268762432957360427 5470573903143649436040641)
              ·
                refine ⟨4102930427357737077030481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5470573903143649436040641 4102930427357737077030481)
                ·
                  refine ⟨3077197820518302807772861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4102930427357737077030481 3077197820518302807772861)
                  ·
                    refine ⟨1153949182694363552914823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3077197820518302807772861 1153949182694363552914823)
                    ·
                      rfl

theorem cell22_3370962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 2, 2, 3].length) (baseStart_3370962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3370962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3370962 prefixEnd_3370962 := by exact prefixLift 3370962
  have htrace : WordTrace (prefixWord ++ tailWord_3370962) baseStart_3370962 baseEnd_3370962 := by
    simpa [prefixWord, tailWord_3370962, baseEnd_3370962] using wordTrace_append hprefix tailTrace_3370962
  have hstable : (prefixWord ++ tailWord_3370962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370962).length < 2 ^ (prefixWord ++ tailWord_3370962).sum := by decide
  have hdescent : baseEnd_3370962 < baseStart_3370962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371016 : List Nat := [2, 1, 3, 2, 1, 2, 1, 5, 1, 4]
def baseStart_3371016 : Nat := 118140960795 + 3371016 * 2 ^ 59
def prefixEnd_3371016 : Nat := 4983230072969 + 3 ^ 40 * 3371016 * 2
def baseEnd_3371016 : Nat := 1153967667997925412064657

theorem tailTrace_3371016 : CollatzResearch.WordTrace tailWord_3371016 prefixEnd_3371016 1153967667997925412064657 := by
  unfold tailWord_3371016
  simp only [CollatzResearch.WordTrace]
  refine ⟨61475527177696115271102451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81967369570261487028136601 61475527177696115271102451)
  ·
    refine ⟨92213290766544172906653677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61475527177696115271102451 92213290766544172906653677)
    ·
      refine ⟨34579984037454064839995129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92213290766544172906653677 34579984037454064839995129)
      ·
        refine ⟨25934988028090548629996347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34579984037454064839995129 25934988028090548629996347)
        ·
          refine ⟨38902482042135822944994521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25934988028090548629996347 38902482042135822944994521)
          ·
            refine ⟨29176861531601867208745891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38902482042135822944994521 29176861531601867208745891)
            ·
              refine ⟨43765292297402800813118837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29176861531601867208745891 43765292297402800813118837)
              ·
                refine ⟨4102996152881512576229891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43765292297402800813118837 4102996152881512576229891)
                ·
                  refine ⟨6154494229322268864344837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4102996152881512576229891 6154494229322268864344837)
                  ·
                    refine ⟨1153967667997925412064657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6154494229322268864344837 1153967667997925412064657)
                    ·
                      rfl

theorem cell22_3371016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 5, 1, 4].length) (baseStart_3371016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3371016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3371016 prefixEnd_3371016 := by exact prefixLift 3371016
  have htrace : WordTrace (prefixWord ++ tailWord_3371016) baseStart_3371016 baseEnd_3371016 := by
    simpa [prefixWord, tailWord_3371016, baseEnd_3371016] using wordTrace_append hprefix tailTrace_3371016
  have hstable : (prefixWord ++ tailWord_3371016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371016).length < 2 ^ (prefixWord ++ tailWord_3371016).sum := by decide
  have hdescent : baseEnd_3371016 < baseStart_3371016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371050 : List Nat := [3, 1, 4, 1, 2, 3, 1, 2, 1, 4]
def baseStart_3371050 : Nat := 118140960795 + 3371050 * 2 ^ 59
def prefixEnd_3371050 : Nat := 4983230072969 + 3 ^ 40 * 3371050 * 2
def baseEnd_3371050 : Nat := 1153979306892760656714553

theorem tailTrace_3371050 : CollatzResearch.WordTrace tailWord_3371050 prefixEnd_3371050 1153979306892760656714553 := by
  unfold tailWord_3371050
  simp only [CollatzResearch.WordTrace]
  refine ⟨30738073609317263587235651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81968196291512702899295069 30738073609317263587235651)
  ·
    refine ⟨46107110413975895380853477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30738073609317263587235651 46107110413975895380853477)
    ·
      refine ⟨8645083202620480383910027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46107110413975895380853477 8645083202620480383910027)
      ·
        refine ⟨12967624803930720575865041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8645083202620480383910027 12967624803930720575865041)
        ·
          refine ⟨9725718602948040431898781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12967624803930720575865041 9725718602948040431898781)
          ·
            refine ⟨3647144476105515161962043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9725718602948040431898781 3647144476105515161962043)
            ·
              refine ⟨5470716714158272742943065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3647144476105515161962043 5470716714158272742943065)
              ·
                refine ⟨4103037535618704557207299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5470716714158272742943065 4103037535618704557207299)
                ·
                  refine ⟨6154556303428056835810949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4103037535618704557207299 6154556303428056835810949)
                  ·
                    refine ⟨1153979306892760656714553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6154556303428056835810949 1153979306892760656714553)
                    ·
                      rfl

theorem cell22_3371050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_3371050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3371050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3371050 prefixEnd_3371050 := by exact prefixLift 3371050
  have htrace : WordTrace (prefixWord ++ tailWord_3371050) baseStart_3371050 baseEnd_3371050 := by
    simpa [prefixWord, tailWord_3371050, baseEnd_3371050] using wordTrace_append hprefix tailTrace_3371050
  have hstable : (prefixWord ++ tailWord_3371050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371050).length < 2 ^ (prefixWord ++ tailWord_3371050).sum := by decide
  have hdescent : baseEnd_3371050 < baseStart_3371050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371059 : List Nat := [1, 1, 1, 2, 4, 1, 4, 8]
def baseStart_3371059 : Nat := 118140960795 + 3371059 * 2 ^ 59
def prefixEnd_3371059 : Nat := 4983230072969 + 3 ^ 40 * 3371059 * 2
def baseEnd_3371059 : Nat := 128220265308520848137725

theorem tailTrace_3371059 : CollatzResearch.WordTrace tailWord_3371059 prefixEnd_3371059 128220265308520848137725 := by
  unfold tailWord_3371059
  simp only [CollatzResearch.WordTrace]
  refine ⟨122952622694236448886020231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81968415129490965924013487 122952622694236448886020231)
  ·
    refine ⟨184428934041354673329030347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122952622694236448886020231 184428934041354673329030347)
    ·
      refine ⟨276643401062032009993545521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184428934041354673329030347 276643401062032009993545521)
      ·
        refine ⟨207482550796524007495159141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276643401062032009993545521 207482550796524007495159141)
        ·
          refine ⟨38902978274348251405342339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 207482550796524007495159141 38902978274348251405342339)
          ·
            refine ⟨58354467411522377108013509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38902978274348251405342339 58354467411522377108013509)
            ·
              refine ⟨10941462639660445707752533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58354467411522377108013509 10941462639660445707752533)
              ·
                refine ⟨128220265308520848137725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10941462639660445707752533 128220265308520848137725)
                ·
                  rfl

theorem cell22_3371059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 8].length) (baseStart_3371059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3371059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3371059 prefixEnd_3371059 := by exact prefixLift 3371059
  have htrace : WordTrace (prefixWord ++ tailWord_3371059) baseStart_3371059 baseEnd_3371059 := by
    simpa [prefixWord, tailWord_3371059, baseEnd_3371059] using wordTrace_append hprefix tailTrace_3371059
  have hstable : (prefixWord ++ tailWord_3371059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371059).length < 2 ^ (prefixWord ++ tailWord_3371059).sum := by decide
  have hdescent : baseEnd_3371059 < baseStart_3371059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371061 : List Nat := [1, 3, 3, 1, 1, 1, 3, 3, 2, 4]
def baseStart_3371061 : Nat := 118140960795 + 3371061 * 2 ^ 59
def prefixEnd_3371061 : Nat := 4983230072969 + 3 ^ 40 * 3371061 * 2
def baseEnd_3371061 : Nat := 1153983072417560294689519

theorem tailTrace_3371061 : CollatzResearch.WordTrace tailWord_3371061 prefixEnd_3371061 1153983072417560294689519 := by
  unfold tailWord_3371061
  simp only [CollatzResearch.WordTrace]
  refine ⟨122952695640229203227593037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81968463760152802151728691 122952695640229203227593037)
  ·
    refine ⟨46107260865085951210347389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122952695640229203227593037 46107260865085951210347389)
    ·
      refine ⟨17290222824407231703880271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46107260865085951210347389 17290222824407231703880271)
      ·
        refine ⟨25935334236610847555820407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17290222824407231703880271 25935334236610847555820407)
        ·
          refine ⟨38903001354916271333730611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25935334236610847555820407 38903001354916271333730611)
          ·
            refine ⟨58354502032374407000595917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38903001354916271333730611 58354502032374407000595917)
            ·
              refine ⟨21882938262140402625223469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58354502032374407000595917 21882938262140402625223469)
              ·
                refine ⟨8206101848302650984458801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21882938262140402625223469 8206101848302650984458801)
                ·
                  refine ⟨6154576386226988238344101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8206101848302650984458801 6154576386226988238344101)
                  ·
                    refine ⟨1153983072417560294689519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6154576386226988238344101 1153983072417560294689519)
                    ·
                      rfl

theorem cell22_3371061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_3371061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3371061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3371061 prefixEnd_3371061 := by exact prefixLift 3371061
  have htrace : WordTrace (prefixWord ++ tailWord_3371061) baseStart_3371061 baseEnd_3371061 := by
    simpa [prefixWord, tailWord_3371061, baseEnd_3371061] using wordTrace_append hprefix tailTrace_3371061
  have hstable : (prefixWord ++ tailWord_3371061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371061).length < 2 ^ (prefixWord ++ tailWord_3371061).sum := by decide
  have hdescent : baseEnd_3371061 < baseStart_3371061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371168 : List Nat := [2, 1, 1, 4, 2, 2, 1, 4, 1, 4]
def baseStart_3371168 : Nat := 118140960795 + 3371168 * 2 ^ 59
def prefixEnd_3371168 : Nat := 4983230072969 + 3 ^ 40 * 3371168 * 2
def baseEnd_3371168 : Nat := 1154019700704247682264191

theorem tailTrace_3371168 : CollatzResearch.WordTrace tailWord_3371168 prefixEnd_3371168 1154019700704247682264191 := by
  unfold tailWord_3371168
  simp only [CollatzResearch.WordTrace]
  refine ⟨61478299125420780250869079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81971065500561040334492105 61478299125420780250869079)
  ·
    refine ⟨92217448688131170376303619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61478299125420780250869079 92217448688131170376303619)
    ·
      refine ⟨138326173032196755564455429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92217448688131170376303619 138326173032196755564455429)
      ·
        refine ⟨25936157443536891668335393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138326173032196755564455429 25936157443536891668335393)
        ·
          refine ⟨19452118082652668751251545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25936157443536891668335393 19452118082652668751251545)
          ·
            refine ⟨14589088561989501563438659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19452118082652668751251545 14589088561989501563438659)
            ·
              refine ⟨21883632842984252345157989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14589088561989501563438659 21883632842984252345157989)
              ·
                refine ⟨4103181158059547314717123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21883632842984252345157989 4103181158059547314717123)
                ·
                  refine ⟨6154771737089320972075685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4103181158059547314717123 6154771737089320972075685)
                  ·
                    refine ⟨1154019700704247682264191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6154771737089320972075685 1154019700704247682264191)
                    ·
                      rfl

theorem cell22_3371168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 4, 1, 4].length) (baseStart_3371168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3371168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3371168 prefixEnd_3371168 := by exact prefixLift 3371168
  have htrace : WordTrace (prefixWord ++ tailWord_3371168) baseStart_3371168 baseEnd_3371168 := by
    simpa [prefixWord, tailWord_3371168, baseEnd_3371168] using wordTrace_append hprefix tailTrace_3371168
  have hstable : (prefixWord ++ tailWord_3371168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371168).length < 2 ^ (prefixWord ++ tailWord_3371168).sum := by decide
  have hdescent : baseEnd_3371168 < baseStart_3371168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371211 : List Nat := [1, 1, 1, 1, 3, 2, 6, 7]
def baseStart_3371211 : Nat := 118140960795 + 3371211 * 2 ^ 59
def prefixEnd_3371211 : Nat := 4983230072969 + 3 ^ 40 * 3371211 * 2
def baseEnd_3371211 : Nat := 128226046720334433715451

theorem tailTrace_3371211 : CollatzResearch.WordTrace tailWord_3371211 prefixEnd_3371211 128226046720334433715451 := by
  unfold tailWord_3371211
  simp only [CollatzResearch.WordTrace]
  refine ⟨122958166589685778845553487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81972111059790519230368991 122958166589685778845553487)
  ·
    refine ⟨184437249884528668268330231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122958166589685778845553487 184437249884528668268330231)
    ·
      refine ⟨276655874826793002402495347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184437249884528668268330231 276655874826793002402495347)
      ·
        refine ⟨414983812240189503603743021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276655874826793002402495347 414983812240189503603743021)
        ·
          refine ⟨155618929590071063851403633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 414983812240189503603743021 155618929590071063851403633)
          ·
            refine ⟨116714197192553297888552725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155618929590071063851403633 116714197192553297888552725)
            ·
              refine ⟨5470977993400935838525909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 116714197192553297888552725 5470977993400935838525909)
              ·
                refine ⟨128226046720334433715451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5470977993400935838525909 128226046720334433715451)
                ·
                  rfl

theorem cell22_3371211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 7].length) (baseStart_3371211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3371211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3371211 prefixEnd_3371211 := by exact prefixLift 3371211
  have htrace : WordTrace (prefixWord ++ tailWord_3371211) baseStart_3371211 baseEnd_3371211 := by
    simpa [prefixWord, tailWord_3371211, baseEnd_3371211] using wordTrace_append hprefix tailTrace_3371211
  have hstable : (prefixWord ++ tailWord_3371211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371211).length < 2 ^ (prefixWord ++ tailWord_3371211).sum := by decide
  have hdescent : baseEnd_3371211 < baseStart_3371211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371226 : List Nat := [3, 1, 1, 2, 2, 1, 2, 1, 2, 7]
def baseStart_3371226 : Nat := 118140960795 + 3371226 * 2 ^ 59
def prefixEnd_3371226 : Nat := 4983230072969 + 3 ^ 40 * 3371226 * 2
def baseEnd_3371226 : Nat := 1154039555289554864314013

theorem tailTrace_3371226 : CollatzResearch.WordTrace tailWord_3371226 prefixEnd_3371226 1154039555289554864314013 := by
  unfold tailWord_3371226
  simp only [CollatzResearch.WordTrace]
  refine ⟨30739678421157859101837383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81972475789754290938233021 30739678421157859101837383)
  ·
    refine ⟨46109517631736788652756075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30739678421157859101837383 46109517631736788652756075)
    ·
      refine ⟨69164276447605182979134113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46109517631736788652756075 69164276447605182979134113)
      ·
        refine ⟨51873207335703887234350585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69164276447605182979134113 51873207335703887234350585)
        ·
          refine ⟨38904905501777915425762939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51873207335703887234350585 38904905501777915425762939)
          ·
            refine ⟨58357358252666873138644409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38904905501777915425762939 58357358252666873138644409)
            ·
              refine ⟨43768018689500154853983307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58357358252666873138644409 43768018689500154853983307)
              ·
                refine ⟨65652028034250232280974961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43768018689500154853983307 65652028034250232280974961)
                ·
                  refine ⟨49239021025687674210731221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65652028034250232280974961 49239021025687674210731221)
                  ·
                    refine ⟨1154039555289554864314013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49239021025687674210731221 1154039555289554864314013)
                    ·
                      rfl

theorem cell22_3371226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 2, 7].length) (baseStart_3371226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3371226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3371226 prefixEnd_3371226 := by exact prefixLift 3371226
  have htrace : WordTrace (prefixWord ++ tailWord_3371226) baseStart_3371226 baseEnd_3371226 := by
    simpa [prefixWord, tailWord_3371226, baseEnd_3371226] using wordTrace_append hprefix tailTrace_3371226
  have hstable : (prefixWord ++ tailWord_3371226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371226).length < 2 ^ (prefixWord ++ tailWord_3371226).sum := by decide
  have hdescent : baseEnd_3371226 < baseStart_3371226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
