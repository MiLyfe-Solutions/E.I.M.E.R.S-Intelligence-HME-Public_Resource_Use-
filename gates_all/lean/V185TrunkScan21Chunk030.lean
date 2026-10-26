import V185TrunkScan21Chunk029

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_363420 : List Nat := [2, 2, 3, 3, 2, 1, 8]
def baseStart_363420 : Nat := 118140960795 + 363420 * 2 ^ 59
def prefixEnd_363420 : Nat := 4983230072969 + 3 ^ 40 * 363420 * 2
def baseEnd_363420 : Nat := 9215266146028313643391

theorem tailTrace_363420 : CollatzResearch.WordTrace tailWord_363420 prefixEnd_363420 9215266146028313643391 := by
  unfold tailWord_363420
  simp only [CollatzResearch.WordTrace]
  refine ⟨6627508171699441019843857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8836677562265921359791809 6627508171699441019843857)
  ·
    refine ⟨4970631128774580764882893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6627508171699441019843857 4970631128774580764882893)
    ·
      refine ⟨1863986673290467786831085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4970631128774580764882893 1863986673290467786831085)
      ·
        refine ⟨698995002483925420061657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1863986673290467786831085 698995002483925420061657)
        ·
          refine ⟨524246251862944065046243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 698995002483925420061657 524246251862944065046243)
          ·
            refine ⟨786369377794416097569365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 524246251862944065046243 786369377794416097569365)
            ·
              refine ⟨9215266146028313643391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 786369377794416097569365 9215266146028313643391)
              ·
                rfl

theorem cell21_363420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 8].length) (baseStart_363420 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_363420 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_363420 prefixEnd_363420 := by exact prefixLift 363420
  have htrace : WordTrace (prefixWord ++ tailWord_363420) baseStart_363420 baseEnd_363420 := by
    simpa [prefixWord, tailWord_363420, baseEnd_363420] using wordTrace_append hprefix tailTrace_363420
  have hstable : (prefixWord ++ tailWord_363420).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363420).length < 2 ^ (prefixWord ++ tailWord_363420).sum := by decide
  have hdescent : baseEnd_363420 < baseStart_363420 := by decide
  rcases family_descends (prefixWord ++ tailWord_363420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363485 : List Nat := [1, 4, 3, 1, 2, 2, 3, 2, 3]
def baseStart_363485 : Nat := 118140960795 + 363485 * 2 ^ 59
def prefixEnd_363485 : Nat := 4983230072969 + 3 ^ 40 * 363485 * 2
def baseEnd_363485 : Nat := 82952229199829154207053

theorem tailTrace_363485 : CollatzResearch.WordTrace tailWord_363485 prefixEnd_363485 82952229199829154207053 := by
  unfold tailWord_363485
  simp only [CollatzResearch.WordTrace]
  refine ⟨13257387088163398140803909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8838258058775598760535939 13257387088163398140803909)
  ·
    refine ⟨2485760079030637151400733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13257387088163398140803909 2485760079030637151400733)
    ·
      refine ⟨932160029636488931775275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2485760079030637151400733 932160029636488931775275)
      ·
        refine ⟨1398240044454733397662913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 932160029636488931775275 1398240044454733397662913)
        ·
          refine ⟨1048680033341050048247185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1398240044454733397662913 1048680033341050048247185)
          ·
            refine ⟨786510025005787536185389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1048680033341050048247185 786510025005787536185389)
            ·
              refine ⟨294941259377170326069521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 786510025005787536185389 294941259377170326069521)
              ·
                refine ⟨221205944532877744552141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 294941259377170326069521 221205944532877744552141)
                ·
                  refine ⟨82952229199829154207053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 221205944532877744552141 82952229199829154207053)
                  ·
                    rfl

theorem cell21_363485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3, 2, 3].length) (baseStart_363485 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_363485 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_363485 prefixEnd_363485 := by exact prefixLift 363485
  have htrace : WordTrace (prefixWord ++ tailWord_363485) baseStart_363485 baseEnd_363485 := by
    simpa [prefixWord, tailWord_363485, baseEnd_363485] using wordTrace_append hprefix tailTrace_363485
  have hstable : (prefixWord ++ tailWord_363485).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363485).length < 2 ^ (prefixWord ++ tailWord_363485).sum := by decide
  have hdescent : baseEnd_363485 < baseStart_363485 := by decide
  rcases family_descends (prefixWord ++ tailWord_363485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363527 : List Nat := [1, 1, 4, 3, 1, 1, 2, 5, 3]
def baseStart_363527 : Nat := 118140960795 + 363527 * 2 ^ 59
def prefixEnd_363527 : Nat := 4983230072969 + 3 ^ 40 * 363527 * 2
def baseEnd_363527 : Nat := 82961814172046414506967

theorem tailTrace_363527 : CollatzResearch.WordTrace tailWord_363527 prefixEnd_363527 82961814172046414506967 := by
  unfold tailWord_363527
  simp only [CollatzResearch.WordTrace]
  refine ⟨13258918954011239313832835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8839279302674159542555223 13258918954011239313832835)
  ·
    refine ⟨19888378431016858970749253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13258918954011239313832835 19888378431016858970749253)
    ·
      refine ⟨3729070955815661057015485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19888378431016858970749253 3729070955815661057015485)
      ·
        refine ⟨1398401608430872896380807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3729070955815661057015485 1398401608430872896380807)
        ·
          refine ⟨2097602412646309344571211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1398401608430872896380807 2097602412646309344571211)
          ·
            refine ⟨3146403618969464016856817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2097602412646309344571211 3146403618969464016856817)
            ·
              refine ⟨2359802714227098012642613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3146403618969464016856817 2359802714227098012642613)
              ·
                refine ⟨221231504458790438685245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2359802714227098012642613 221231504458790438685245)
                ·
                  refine ⟨82961814172046414506967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 221231504458790438685245 82961814172046414506967)
                  ·
                    rfl

theorem cell21_363527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 5, 3].length) (baseStart_363527 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_363527 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_363527 prefixEnd_363527 := by exact prefixLift 363527
  have htrace : WordTrace (prefixWord ++ tailWord_363527) baseStart_363527 baseEnd_363527 := by
    simpa [prefixWord, tailWord_363527, baseEnd_363527] using wordTrace_append hprefix tailTrace_363527
  have hstable : (prefixWord ++ tailWord_363527).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363527).length < 2 ^ (prefixWord ++ tailWord_363527).sum := by decide
  have hdescent : baseEnd_363527 < baseStart_363527 := by decide
  rcases family_descends (prefixWord ++ tailWord_363527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363541 : List Nat := [1, 3, 2, 1, 4, 1, 1, 4, 4]
def baseStart_363541 : Nat := 118140960795 + 363541 * 2 ^ 59
def prefixEnd_363541 : Nat := 4983230072969 + 3 ^ 40 * 363541 * 2
def baseEnd_363541 : Nat := 82965009162785501273605

theorem tailTrace_363541 : CollatzResearch.WordTrace tailWord_363541 prefixEnd_363541 82965009162785501273605 := by
  unfold tailWord_363541
  simp only [CollatzResearch.WordTrace]
  refine ⟨13259429575960519704842477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8839619717307013136561651 13259429575960519704842477)
  ·
    refine ⟨4972286090985194889315929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13259429575960519704842477 4972286090985194889315929)
    ·
      refine ⟨3729214568238896166986947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4972286090985194889315929 3729214568238896166986947)
      ·
        refine ⟨5593821852358344250480421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3729214568238896166986947 5593821852358344250480421)
        ·
          refine ⟨1048841597317189546965079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5593821852358344250480421 1048841597317189546965079)
          ·
            refine ⟨1573262395975784320447619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1048841597317189546965079 1573262395975784320447619)
            ·
              refine ⟨2359893593963676480671429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1573262395975784320447619 2359893593963676480671429)
              ·
                refine ⟨442480048868189340125893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2359893593963676480671429 442480048868189340125893)
                ·
                  refine ⟨82965009162785501273605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 442480048868189340125893 82965009162785501273605)
                  ·
                    rfl

theorem cell21_363541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 4, 4].length) (baseStart_363541 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_363541 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_363541 prefixEnd_363541 := by exact prefixLift 363541
  have htrace : WordTrace (prefixWord ++ tailWord_363541) baseStart_363541 baseEnd_363541 := by
    simpa [prefixWord, tailWord_363541, baseEnd_363541] using wordTrace_append hprefix tailTrace_363541
  have hstable : (prefixWord ++ tailWord_363541).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363541).length < 2 ^ (prefixWord ++ tailWord_363541).sum := by decide
  have hdescent : baseEnd_363541 < baseStart_363541 := by decide
  rcases family_descends (prefixWord ++ tailWord_363541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363544 : List Nat := [2, 1, 2, 3, 2, 2, 4, 2, 3]
def baseStart_363544 : Nat := 118140960795 + 363544 * 2 ^ 59
def prefixEnd_363544 : Nat := 4983230072969 + 3 ^ 40 * 363544 * 2
def baseEnd_363544 : Nat := 82965693803658162723599

theorem tailTrace_363544 : CollatzResearch.WordTrace tailWord_363544 prefixEnd_363544 82965693803658162723599 := by
  unfold tailWord_363544
  simp only [CollatzResearch.WordTrace]
  refine ⟨6629769497474825608600843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8839692663299767478134457 6629769497474825608600843)
  ·
    refine ⟨9944654246212238412901265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6629769497474825608600843 9944654246212238412901265)
    ·
      refine ⟨7458490684659178809675949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9944654246212238412901265 7458490684659178809675949)
      ·
        refine ⟨2796934006747192053628481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7458490684659178809675949 2796934006747192053628481)
        ·
          refine ⟨2097700505060394040221361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2796934006747192053628481 2097700505060394040221361)
          ·
            refine ⟨1573275378795295530166021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2097700505060394040221361 1573275378795295530166021)
            ·
              refine ⟨294989133524117911906129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1573275378795295530166021 294989133524117911906129)
              ·
                refine ⟨221241850143088433929597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 294989133524117911906129 221241850143088433929597)
                ·
                  refine ⟨82965693803658162723599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 221241850143088433929597 82965693803658162723599)
                  ·
                    rfl

theorem cell21_363544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4, 2, 3].length) (baseStart_363544 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_363544 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_363544 prefixEnd_363544 := by exact prefixLift 363544
  have htrace : WordTrace (prefixWord ++ tailWord_363544) baseStart_363544 baseEnd_363544 := by
    simpa [prefixWord, tailWord_363544, baseEnd_363544] using wordTrace_append hprefix tailTrace_363544
  have hstable : (prefixWord ++ tailWord_363544).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363544).length < 2 ^ (prefixWord ++ tailWord_363544).sum := by decide
  have hdescent : baseEnd_363544 < baseStart_363544 := by decide
  rcases family_descends (prefixWord ++ tailWord_363544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363555 : List Nat := [1, 1, 1, 4, 3, 2, 3, 6]
def baseStart_363555 : Nat := 118140960795 + 363555 * 2 ^ 59
def prefixEnd_363555 : Nat := 4983230072969 + 3 ^ 40 * 363555 * 2
def baseEnd_363555 : Nat := 27656068051174862680081

theorem tailTrace_363555 : CollatzResearch.WordTrace tailWord_363555 prefixEnd_363555 27656068051174862680081 := by
  unfold tailWord_363555
  simp only [CollatzResearch.WordTrace]
  refine ⟨13259940197909800095852119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8839960131939866730568079 13259940197909800095852119)
  ·
    refine ⟨19889910296864700143778179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13259940197909800095852119 19889910296864700143778179)
    ·
      refine ⟨29834865445297050215667269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19889910296864700143778179 29834865445297050215667269)
      ·
        refine ⟨5594037270993196915437613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29834865445297050215667269 5594037270993196915437613)
        ·
          refine ⟨2097763976622448843289105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5594037270993196915437613 2097763976622448843289105)
          ·
            refine ⟨1573322982466836632466829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2097763976622448843289105 1573322982466836632466829)
            ·
              refine ⟨589996118425063737175061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1573322982466836632466829 589996118425063737175061)
              ·
                refine ⟨27656068051174862680081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 589996118425063737175061 27656068051174862680081)
                ·
                  rfl

theorem cell21_363555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 6].length) (baseStart_363555 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_363555 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_363555 prefixEnd_363555 := by exact prefixLift 363555
  have htrace : WordTrace (prefixWord ++ tailWord_363555) baseStart_363555 baseEnd_363555 := by
    simpa [prefixWord, tailWord_363555, baseEnd_363555] using wordTrace_append hprefix tailTrace_363555
  have hstable : (prefixWord ++ tailWord_363555).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363555).length < 2 ^ (prefixWord ++ tailWord_363555).sum := by decide
  have hdescent : baseEnd_363555 < baseStart_363555 := by decide
  rcases family_descends (prefixWord ++ tailWord_363555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363710 : List Nat := [4, 2, 1, 1, 3, 2, 2, 2, 4]
def baseStart_363710 : Nat := 118140960795 + 363710 * 2 ^ 59
def prefixEnd_363710 : Nat := 4983230072969 + 3 ^ 40 * 363710 * 2
def baseEnd_363710 : Nat := 83003577265278762956593

theorem tailTrace_363710 : CollatzResearch.WordTrace tailWord_363710 prefixEnd_363710 83003577265278762956593 := by
  unfold tailWord_363710
  simp only [CollatzResearch.WordTrace]
  refine ⟨1658199189043532695968073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8843729008232174378496389 1658199189043532695968073)
  ·
    refine ⟨1243649391782649521976055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1658199189043532695968073 1243649391782649521976055)
    ·
      refine ⟨1865474087673974282964083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1243649391782649521976055 1865474087673974282964083)
      ·
        refine ⟨2798211131510961424446125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1865474087673974282964083 2798211131510961424446125)
        ·
          refine ⟨1049329174316610534167297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2798211131510961424446125 1049329174316610534167297)
          ·
            refine ⟨786996880737457900625473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1049329174316610534167297 786996880737457900625473)
            ·
              refine ⟨590247660553093425469105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 786996880737457900625473 590247660553093425469105)
              ·
                refine ⟨442685745414820069101829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 590247660553093425469105 442685745414820069101829)
                ·
                  refine ⟨83003577265278762956593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 442685745414820069101829 83003577265278762956593)
                  ·
                    rfl

theorem cell21_363710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_363710 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_363710 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_363710 prefixEnd_363710 := by exact prefixLift 363710
  have htrace : WordTrace (prefixWord ++ tailWord_363710) baseStart_363710 baseEnd_363710 := by
    simpa [prefixWord, tailWord_363710, baseEnd_363710] using wordTrace_append hprefix tailTrace_363710
  have hstable : (prefixWord ++ tailWord_363710).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363710).length < 2 ^ (prefixWord ++ tailWord_363710).sum := by decide
  have hdescent : baseEnd_363710 < baseStart_363710 := by decide
  rcases family_descends (prefixWord ++ tailWord_363710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363713 : List Nat := [1, 2, 6, 1, 1, 1, 4, 2, 3]
def baseStart_363713 : Nat := 118140960795 + 363713 * 2 ^ 59
def prefixEnd_363713 : Nat := 4983230072969 + 3 ^ 40 * 363713 * 2
def baseEnd_363713 : Nat := 83004261906151424406587

theorem tailTrace_363713 : CollatzResearch.WordTrace tailWord_363713 prefixEnd_363713 83004261906151424406587 := by
  unfold tailWord_363713
  simp only [CollatzResearch.WordTrace]
  refine ⟨13265702931337393080103793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8843801954224928720069195 13265702931337393080103793)
  ·
    refine ⟨9949277198503044810077845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13265702931337393080103793 9949277198503044810077845)
    ·
      refine ⟨466372368679830225472399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9949277198503044810077845 466372368679830225472399)
      ·
        refine ⟨699558553019745338208599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 466372368679830225472399 699558553019745338208599)
        ·
          refine ⟨1049337829529618007312899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 699558553019745338208599 1049337829529618007312899)
          ·
            refine ⟨1574006744294427010969349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1049337829529618007312899 1574006744294427010969349)
            ·
              refine ⟨295126264555205064556753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1574006744294427010969349 295126264555205064556753)
              ·
                refine ⟨221344698416403798417565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 295126264555205064556753 221344698416403798417565)
                ·
                  refine ⟨83004261906151424406587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 221344698416403798417565 83004261906151424406587)
                  ·
                    rfl

theorem cell21_363713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4, 2, 3].length) (baseStart_363713 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_363713 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_363713 prefixEnd_363713 := by exact prefixLift 363713
  have htrace : WordTrace (prefixWord ++ tailWord_363713) baseStart_363713 baseEnd_363713 := by
    simpa [prefixWord, tailWord_363713, baseEnd_363713] using wordTrace_append hprefix tailTrace_363713
  have hstable : (prefixWord ++ tailWord_363713).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363713).length < 2 ^ (prefixWord ++ tailWord_363713).sum := by decide
  have hdescent : baseEnd_363713 < baseStart_363713 := by decide
  rcases family_descends (prefixWord ++ tailWord_363713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363741 : List Nat := [1, 4, 3, 2, 2, 1, 3, 5]
def baseStart_363741 : Nat := 118140960795 + 363741 * 2 ^ 59
def prefixEnd_363741 : Nat := 4983230072969 + 3 ^ 40 * 363741 * 2
def baseEnd_363741 : Nat := 27670217295876532646621

theorem tailTrace_363741 : CollatzResearch.WordTrace tailWord_363741 prefixEnd_363741 27670217295876532646621 := by
  unfold tailWord_363741
  simp only [CollatzResearch.WordTrace]
  refine ⟨13266724175235953862123077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8844482783490635908082051 13266724175235953862123077)
  ·
    refine ⟨2487510782856741349148077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13266724175235953862123077 2487510782856741349148077)
    ·
      refine ⟨932816543571278005930529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2487510782856741349148077 932816543571278005930529)
      ·
        refine ⟨699612407678458504447897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 932816543571278005930529 699612407678458504447897)
        ·
          refine ⟨524709305758843878335923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 699612407678458504447897 524709305758843878335923)
          ·
            refine ⟨787063958638265817503885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 524709305758843878335923 787063958638265817503885)
            ·
              refine ⟨295148984489349681563957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 787063958638265817503885 295148984489349681563957)
              ·
                refine ⟨27670217295876532646621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 295148984489349681563957 27670217295876532646621)
                ·
                  rfl

theorem cell21_363741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3, 5].length) (baseStart_363741 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_363741 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_363741 prefixEnd_363741 := by exact prefixLift 363741
  have htrace : WordTrace (prefixWord ++ tailWord_363741) baseStart_363741 baseEnd_363741 := by
    simpa [prefixWord, tailWord_363741, baseEnd_363741] using wordTrace_append hprefix tailTrace_363741
  have hstable : (prefixWord ++ tailWord_363741).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363741).length < 2 ^ (prefixWord ++ tailWord_363741).sum := by decide
  have hdescent : baseEnd_363741 < baseStart_363741 := by decide
  rcases family_descends (prefixWord ++ tailWord_363741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363752 : List Nat := [2, 1, 4, 1, 2, 1, 2, 2, 6]
def baseStart_363752 : Nat := 118140960795 + 363752 * 2 ^ 59
def prefixEnd_363752 : Nat := 4983230072969 + 3 ^ 40 * 363752 * 2
def baseEnd_363752 : Nat := 83013162237496023256507

theorem tailTrace_363752 : CollatzResearch.WordTrace tailWord_363752 prefixEnd_363752 83013162237496023256507 := by
  unfold tailWord_363752
  simp only [CollatzResearch.WordTrace]
  refine ⟨6633562689098051370386755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8844750252130735160515673 6633562689098051370386755)
  ·
    refine ⟨9950344033647077055580133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6633562689098051370386755 9950344033647077055580133)
    ·
      refine ⟨1865689506308826947921275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9950344033647077055580133 1865689506308826947921275)
      ·
        refine ⟨2798534259463240421881913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1865689506308826947921275 2798534259463240421881913)
        ·
          refine ⟨2098900694597430316411435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2798534259463240421881913 2098900694597430316411435)
          ·
            refine ⟨3148351041896145474617153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2098900694597430316411435 3148351041896145474617153)
            ·
              refine ⟨2361263281422109105962865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3148351041896145474617153 2361263281422109105962865)
              ·
                refine ⟨1770947461066581829472149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2361263281422109105962865 1770947461066581829472149)
                ·
                  refine ⟨83013162237496023256507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1770947461066581829472149 83013162237496023256507)
                  ·
                    rfl

theorem cell21_363752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 6].length) (baseStart_363752 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_363752 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_363752 prefixEnd_363752 := by exact prefixLift 363752
  have htrace : WordTrace (prefixWord ++ tailWord_363752) baseStart_363752 baseEnd_363752 := by
    simpa [prefixWord, tailWord_363752, baseEnd_363752] using wordTrace_append hprefix tailTrace_363752
  have hstable : (prefixWord ++ tailWord_363752).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363752).length < 2 ^ (prefixWord ++ tailWord_363752).sum := by decide
  have hdescent : baseEnd_363752 < baseStart_363752 := by decide
  rcases family_descends (prefixWord ++ tailWord_363752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363755 : List Nat := [1, 1, 1, 1, 2, 7, 2, 3, 3]
def baseStart_363755 : Nat := 118140960795 + 363755 * 2 ^ 59
def prefixEnd_363755 : Nat := 4983230072969 + 3 ^ 40 * 363755 * 2
def baseEnd_363755 : Nat := 83013846878368684706501

theorem tailTrace_363755 : CollatzResearch.WordTrace tailWord_363755 prefixEnd_363755 83013846878368684706501 := by
  unfold tailWord_363755
  simp only [CollatzResearch.WordTrace]
  refine ⟨13267234797185234253132719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8844823198123489502088479 13267234797185234253132719)
  ·
    refine ⟨19900852195777851379699079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13267234797185234253132719 19900852195777851379699079)
    ·
      refine ⟨29851278293666777069548619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19900852195777851379699079 29851278293666777069548619)
      ·
        refine ⟨44776917440500165604322929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29851278293666777069548619 44776917440500165604322929)
        ·
          refine ⟨33582688080375124203242197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44776917440500165604322929 33582688080375124203242197)
          ·
            refine ⟨787094251883791973513489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 33582688080375124203242197 787094251883791973513489)
            ·
              refine ⟨590320688912843980135117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 787094251883791973513489 590320688912843980135117)
              ·
                refine ⟨221370258342316492550669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 590320688912843980135117 221370258342316492550669)
                ·
                  refine ⟨83013846878368684706501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 221370258342316492550669 83013846878368684706501)
                  ·
                    rfl

theorem cell21_363755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 3, 3].length) (baseStart_363755 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_363755 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_363755 prefixEnd_363755 := by exact prefixLift 363755
  have htrace : WordTrace (prefixWord ++ tailWord_363755) baseStart_363755 baseEnd_363755 := by
    simpa [prefixWord, tailWord_363755, baseEnd_363755] using wordTrace_append hprefix tailTrace_363755
  have hstable : (prefixWord ++ tailWord_363755).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363755).length < 2 ^ (prefixWord ++ tailWord_363755).sum := by decide
  have hdescent : baseEnd_363755 < baseStart_363755 := by decide
  rcases family_descends (prefixWord ++ tailWord_363755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363800 : List Nat := [2, 1, 2, 3, 1, 5, 2, 5]
def baseStart_363800 : Nat := 118140960795 + 363800 * 2 ^ 59
def prefixEnd_363800 : Nat := 4983230072969 + 3 ^ 40 * 363800 * 2
def baseEnd_363800 : Nat := 27674705497152868818803

theorem tailTrace_363800 : CollatzResearch.WordTrace tailWord_363800 prefixEnd_363800 27674705497152868818803 := by
  unfold tailWord_363800
  simp only [CollatzResearch.WordTrace]
  refine ⟨6634438041011103469260427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8845917388014804625680569 6634438041011103469260427)
  ·
    refine ⟨9951657061516655203890641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6634438041011103469260427 9951657061516655203890641)
    ·
      refine ⟨7463742796137491402917981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9951657061516655203890641 7463742796137491402917981)
      ·
        refine ⟨2798903548551559276094243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7463742796137491402917981 2798903548551559276094243)
        ·
          refine ⟨4198355322827338914141365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2798903548551559276094243 4198355322827338914141365)
          ·
            refine ⟨393595811515063023200753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4198355322827338914141365 393595811515063023200753)
            ·
              refine ⟨295196858636297267400565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 393595811515063023200753 295196858636297267400565)
              ·
                refine ⟨27674705497152868818803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 295196858636297267400565 27674705497152868818803)
                ·
                  rfl

theorem cell21_363800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2, 5].length) (baseStart_363800 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_363800 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_363800 prefixEnd_363800 := by exact prefixLift 363800
  have htrace : WordTrace (prefixWord ++ tailWord_363800) baseStart_363800 baseEnd_363800 := by
    simpa [prefixWord, tailWord_363800, baseEnd_363800] using wordTrace_append hprefix tailTrace_363800
  have hstable : (prefixWord ++ tailWord_363800).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363800).length < 2 ^ (prefixWord ++ tailWord_363800).sum := by decide
  have hdescent : baseEnd_363800 < baseStart_363800 := by decide
  rcases family_descends (prefixWord ++ tailWord_363800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363806 : List Nat := [4, 3, 2, 1, 2, 2, 1, 3, 3]
def baseStart_363806 : Nat := 118140960795 + 363806 * 2 ^ 59
def prefixEnd_363806 : Nat := 4983230072969 + 3 ^ 40 * 363806 * 2
def baseEnd_363806 : Nat := 83025485773203929356397

theorem tailTrace_363806 : CollatzResearch.WordTrace tailWord_363806 prefixEnd_363806 83025485773203929356397 := by
  unfold tailWord_363806
  simp only [CollatzResearch.WordTrace]
  refine ⟨1658636865000058745404909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8846063280000313308826181 1658636865000058745404909)
  ·
    refine ⟨621988824375022029526841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1658636865000058745404909 621988824375022029526841)
    ·
      refine ⟨466491618281266522145131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 621988824375022029526841 466491618281266522145131)
      ·
        refine ⟨699737427421899783217697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 466491618281266522145131 699737427421899783217697)
        ·
          refine ⟨524803070566424837413273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 699737427421899783217697 524803070566424837413273)
          ·
            refine ⟨393602302924818628059955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 524803070566424837413273 393602302924818628059955)
            ·
              refine ⟨590403454387227942089933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 393602302924818628059955 590403454387227942089933)
              ·
                refine ⟨221401295395210478283725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 590403454387227942089933 221401295395210478283725)
                ·
                  refine ⟨83025485773203929356397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 221401295395210478283725 83025485773203929356397)
                  ·
                    rfl

theorem cell21_363806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_363806 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_363806 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_363806 prefixEnd_363806 := by exact prefixLift 363806
  have htrace : WordTrace (prefixWord ++ tailWord_363806) baseStart_363806 baseEnd_363806 := by
    simpa [prefixWord, tailWord_363806, baseEnd_363806] using wordTrace_append hprefix tailTrace_363806
  have hstable : (prefixWord ++ tailWord_363806).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363806).length < 2 ^ (prefixWord ++ tailWord_363806).sum := by decide
  have hdescent : baseEnd_363806 < baseStart_363806 := by decide
  rcases family_descends (prefixWord ++ tailWord_363806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363882 : List Nat := [3, 1, 3, 3, 3, 1, 2, 2, 3]
def baseStart_363882 : Nat := 118140960795 + 363882 * 2 ^ 59
def prefixEnd_363882 : Nat := 4983230072969 + 3 ^ 40 * 363882 * 2
def baseEnd_363882 : Nat := 83042830008644686089575

theorem tailTrace_363882 : CollatzResearch.WordTrace tailWord_363882 prefixEnd_363882 83042830008644686089575 := by
  unfold tailWord_363882
  simp only [CollatzResearch.WordTrace]
  refine ⟨3317966716931283735751475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8847911245150089962003933 3317966716931283735751475)
  ·
    refine ⟨4976950075396925603627213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3317966716931283735751475 4976950075396925603627213)
    ·
      refine ⟨1866356278273847101360205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4976950075396925603627213 1866356278273847101360205)
      ·
        refine ⟨699883604352692663010077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1866356278273847101360205 699883604352692663010077)
        ·
          refine ⟨262456351632259748628779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 699883604352692663010077 262456351632259748628779)
          ·
            refine ⟨393684527448389622943169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262456351632259748628779 393684527448389622943169)
            ·
              refine ⟨295263395586292217207377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 393684527448389622943169 295263395586292217207377)
              ·
                refine ⟨221447546689719162905533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 295263395586292217207377 221447546689719162905533)
                ·
                  refine ⟨83042830008644686089575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 221447546689719162905533 83042830008644686089575)
                  ·
                    rfl

theorem cell21_363882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 2, 2, 3].length) (baseStart_363882 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_363882 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_363882 prefixEnd_363882 := by exact prefixLift 363882
  have htrace : WordTrace (prefixWord ++ tailWord_363882) baseStart_363882 baseEnd_363882 := by
    simpa [prefixWord, tailWord_363882, baseEnd_363882] using wordTrace_append hprefix tailTrace_363882
  have hstable : (prefixWord ++ tailWord_363882).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363882).length < 2 ^ (prefixWord ++ tailWord_363882).sum := by decide
  have hdescent : baseEnd_363882 < baseStart_363882 := by decide
  rcases family_descends (prefixWord ++ tailWord_363882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363893 : List Nat := [1, 3, 4, 1, 4, 1, 1, 6]
def baseStart_363893 : Nat := 118140960795 + 363893 * 2 ^ 59
def prefixEnd_363893 : Nat := 4983230072969 + 3 ^ 40 * 363893 * 2
def baseEnd_363893 : Nat := 27681780119503703802073

theorem tailTrace_363893 : CollatzResearch.WordTrace tailWord_363893 prefixEnd_363893 27681780119503703802073 := by
  unfold tailWord_363893
  simp only [CollatzResearch.WordTrace]
  refine ⟨13272268070685283821656333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8848178713790189214437555 13272268070685283821656333)
  ·
    refine ⟨4977100526506981433121125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13272268070685283821656333 4977100526506981433121125)
    ·
      refine ⟨933206348720059018710211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4977100526506981433121125 933206348720059018710211)
      ·
        refine ⟨1399809523080088528065317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 933206348720059018710211 1399809523080088528065317)
        ·
          refine ⟨262464285577516599012247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1399809523080088528065317 262464285577516599012247)
          ·
            refine ⟨393696428366274898518371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262464285577516599012247 393696428366274898518371)
            ·
              refine ⟨590544642549412347777557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 393696428366274898518371 590544642549412347777557)
              ·
                refine ⟨27681780119503703802073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 590544642549412347777557 27681780119503703802073)
                ·
                  rfl

theorem cell21_363893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 6].length) (baseStart_363893 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_363893 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_363893 prefixEnd_363893 := by exact prefixLift 363893
  have htrace : WordTrace (prefixWord ++ tailWord_363893) baseStart_363893 baseEnd_363893 := by
    simpa [prefixWord, tailWord_363893, baseEnd_363893] using wordTrace_append hprefix tailTrace_363893
  have hstable : (prefixWord ++ tailWord_363893).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363893).length < 2 ^ (prefixWord ++ tailWord_363893).sum := by decide
  have hdescent : baseEnd_363893 < baseStart_363893 := by decide
  rcases family_descends (prefixWord ++ tailWord_363893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363924 : List Nat := [2, 4, 2, 1, 2, 2, 2, 3, 3]
def baseStart_363924 : Nat := 118140960795 + 363924 * 2 ^ 59
def prefixEnd_363924 : Nat := 4983230072969 + 3 ^ 40 * 363924 * 2
def baseEnd_363924 : Nat := 83052414980861946389489

theorem tailTrace_363924 : CollatzResearch.WordTrace tailWord_363924 prefixEnd_363924 83052414980861946389489 := by
  unfold tailWord_363924
  simp only [CollatzResearch.WordTrace]
  refine ⟨6636699366786488058017413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8848932489048650744023217 6636699366786488058017413)
  ·
    refine ⟨1244381131272466510878265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6636699366786488058017413 1244381131272466510878265)
    ·
      refine ⟨933285848454349883158699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1244381131272466510878265 933285848454349883158699)
      ·
        refine ⟨1399928772681524824738049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 933285848454349883158699 1399928772681524824738049)
        ·
          refine ⟨1049946579511143618553537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1399928772681524824738049 1049946579511143618553537)
          ·
            refine ⟨787459934633357713915153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1049946579511143618553537 787459934633357713915153)
            ·
              refine ⟨590594950975018285436365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 787459934633357713915153 590594950975018285436365)
              ·
                refine ⟨221473106615631857038637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 590594950975018285436365 221473106615631857038637)
                ·
                  refine ⟨83052414980861946389489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 221473106615631857038637 83052414980861946389489)
                  ·
                    rfl

theorem cell21_363924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_363924 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_363924 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_363924 prefixEnd_363924 := by exact prefixLift 363924
  have htrace : WordTrace (prefixWord ++ tailWord_363924) baseStart_363924 baseEnd_363924 := by
    simpa [prefixWord, tailWord_363924, baseEnd_363924] using wordTrace_append hprefix tailTrace_363924
  have hstable : (prefixWord ++ tailWord_363924).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363924).length < 2 ^ (prefixWord ++ tailWord_363924).sum := by decide
  have hdescent : baseEnd_363924 < baseStart_363924 := by decide
  rcases family_descends (prefixWord ++ tailWord_363924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363938 : List Nat := [3, 3, 1, 2, 1, 4, 1, 2, 4]
def baseStart_363938 : Nat := 118140960795 + 363938 * 2 ^ 59
def prefixEnd_363938 : Nat := 4983230072969 + 3 ^ 40 * 363938 * 2
def baseEnd_363938 : Nat := 83055609971601033156127

theorem tailTrace_363938 : CollatzResearch.WordTrace tailWord_363938 prefixEnd_363938 83055609971601033156127 := by
  unfold tailWord_363938
  simp only [CollatzResearch.WordTrace]
  refine ⟨3318477338880564126761117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8849272903681504338029645 3318477338880564126761117)
  ·
    refine ⟨1244429002080211547535419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3318477338880564126761117 1244429002080211547535419)
    ·
      refine ⟨1866643503120317321303129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1244429002080211547535419 1866643503120317321303129)
      ·
        refine ⟨1399982627340237990977347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1866643503120317321303129 1399982627340237990977347)
        ·
          refine ⟨2099973941010356986466021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1399982627340237990977347 2099973941010356986466021)
          ·
            refine ⟨393745113939441934962379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2099973941010356986466021 393745113939441934962379)
            ·
              refine ⟨590617670909162902443569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 393745113939441934962379 590617670909162902443569)
              ·
                refine ⟨442963253181872176832677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 590617670909162902443569 442963253181872176832677)
                ·
                  refine ⟨83055609971601033156127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 442963253181872176832677 83055609971601033156127)
                  ·
                    rfl

theorem cell21_363938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_363938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_363938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_363938 prefixEnd_363938 := by exact prefixLift 363938
  have htrace : WordTrace (prefixWord ++ tailWord_363938) baseStart_363938 baseEnd_363938 := by
    simpa [prefixWord, tailWord_363938, baseEnd_363938] using wordTrace_append hprefix tailTrace_363938
  have hstable : (prefixWord ++ tailWord_363938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363938).length < 2 ^ (prefixWord ++ tailWord_363938).sum := by decide
  have hdescent : baseEnd_363938 < baseStart_363938 := by decide
  rcases family_descends (prefixWord ++ tailWord_363938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363980 : List Nat := [2, 2, 1, 4, 2, 1, 1, 2, 6]
def baseStart_363980 : Nat := 118140960795 + 363980 * 2 ^ 59
def prefixEnd_363980 : Nat := 4983230072969 + 3 ^ 40 * 363980 * 2
def baseEnd_363980 : Nat := 83065194943818293456041

theorem tailTrace_363980 : CollatzResearch.WordTrace tailWord_363980 prefixEnd_363980 83065194943818293456041 := by
  unfold tailWord_363980
  simp only [CollatzResearch.WordTrace]
  refine ⟨6637720610685048840036697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8850294147580065120048929 6637720610685048840036697)
  ·
    refine ⟨4978290458013786630027523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6637720610685048840036697 4978290458013786630027523)
    ·
      refine ⟨7467435687020679945041285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4978290458013786630027523 7467435687020679945041285)
      ·
        refine ⟨1400144191316377489695241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7467435687020679945041285 1400144191316377489695241)
        ·
          refine ⟨1050108143487283117271431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1400144191316377489695241 1050108143487283117271431)
          ·
            refine ⟨1575162215230924675907147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1050108143487283117271431 1575162215230924675907147)
            ·
              refine ⟨2362743322846387013860721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1575162215230924675907147 2362743322846387013860721)
              ·
                refine ⟨1772057492134790260395541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2362743322846387013860721 1772057492134790260395541)
                ·
                  refine ⟨83065194943818293456041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1772057492134790260395541 83065194943818293456041)
                  ·
                    rfl

theorem cell21_363980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 6].length) (baseStart_363980 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_363980 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_363980 prefixEnd_363980 := by exact prefixLift 363980
  have htrace : WordTrace (prefixWord ++ tailWord_363980) baseStart_363980 baseEnd_363980 := by
    simpa [prefixWord, tailWord_363980, baseEnd_363980] using wordTrace_append hprefix tailTrace_363980
  have hstable : (prefixWord ++ tailWord_363980).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363980).length < 2 ^ (prefixWord ++ tailWord_363980).sum := by decide
  have hdescent : baseEnd_363980 < baseStart_363980 := by decide
  rcases family_descends (prefixWord ++ tailWord_363980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363994 : List Nat := [3, 1, 1, 2, 3, 2, 9]
def baseStart_363994 : Nat := 118140960795 + 363994 * 2 ^ 59
def prefixEnd_363994 : Nat := 4983230072969 + 3 ^ 40 * 363994 * 2
def baseEnd_363994 : Nat := 9229821103839708913631

theorem tailTrace_363994 : CollatzResearch.WordTrace tailWord_363994 prefixEnd_363994 9229821103839708913631 := by
  unfold tailWord_363994
  simp only [CollatzResearch.WordTrace]
  refine ⟨3318987960829844517770759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8850634562212918714055357 3318987960829844517770759)
  ·
    refine ⟨4978481941244766776656139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3318987960829844517770759 4978481941244766776656139)
    ·
      refine ⟨7467722911867150164984209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4978481941244766776656139 7467722911867150164984209)
      ·
        refine ⟨5600792183900362623738157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7467722911867150164984209 5600792183900362623738157)
        ·
          refine ⟨2100297068962635983901809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5600792183900362623738157 2100297068962635983901809)
          ·
            refine ⟨1575222801721976987926357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2100297068962635983901809 1575222801721976987926357)
            ·
              refine ⟨9229821103839708913631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1575222801721976987926357 9229821103839708913631)
              ·
                rfl

theorem cell21_363994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 9].length) (baseStart_363994 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_363994 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_363994 prefixEnd_363994 := by exact prefixLift 363994
  have htrace : WordTrace (prefixWord ++ tailWord_363994) baseStart_363994 baseEnd_363994 := by
    simpa [prefixWord, tailWord_363994, baseEnd_363994] using wordTrace_append hprefix tailTrace_363994
  have hstable : (prefixWord ++ tailWord_363994).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363994).length < 2 ^ (prefixWord ++ tailWord_363994).sum := by decide
  have hdescent : baseEnd_363994 < baseStart_363994 := by decide
  rcases family_descends (prefixWord ++ tailWord_363994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364045 : List Nat := [1, 7, 1, 1, 3, 8]
def baseStart_364045 : Nat := 118140960795 + 364045 * 2 ^ 59
def prefixEnd_364045 : Nat := 4983230072969 + 3 ^ 40 * 364045 * 2
def baseEnd_364045 : Nat := 3077038104792319439725

theorem tailTrace_364045 : CollatzResearch.WordTrace tailWord_364045 prefixEnd_364045 3077038104792319439725 := by
  unfold tailWord_364045
  simp only [CollatzResearch.WordTrace]
  refine ⟨13277811966134613781189589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8851874644089742520793059 13277811966134613781189589)
  ·
    refine ⟨311198717956280010496631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 13277811966134613781189589 311198717956280010496631)
    ·
      refine ⟨466798076934420015744947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311198717956280010496631 466798076934420015744947)
      ·
        refine ⟨700197115401630023617421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 466798076934420015744947 700197115401630023617421)
        ·
          refine ⟨262573918275611258856533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 700197115401630023617421 262573918275611258856533)
          ·
            refine ⟨3077038104792319439725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 262573918275611258856533 3077038104792319439725)
            ·
              rfl

theorem cell21_364045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 8].length) (baseStart_364045 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_364045 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_364045 prefixEnd_364045 := by exact prefixLift 364045
  have htrace : WordTrace (prefixWord ++ tailWord_364045) baseStart_364045 baseEnd_364045 := by
    simpa [prefixWord, tailWord_364045, baseEnd_364045] using wordTrace_append hprefix tailTrace_364045
  have hstable : (prefixWord ++ tailWord_364045).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364045).length < 2 ^ (prefixWord ++ tailWord_364045).sum := by decide
  have hdescent : baseEnd_364045 < baseStart_364045 := by decide
  rcases family_descends (prefixWord ++ tailWord_364045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364087 : List Nat := [1, 1, 3, 1, 2, 5, 3, 5]
def baseStart_364087 : Nat := 118140960795 + 364087 * 2 ^ 59
def prefixEnd_364087 : Nat := 4983230072969 + 3 ^ 40 * 364087 * 2
def baseEnd_364087 : Nat := 27696537933869961724163

theorem tailTrace_364087 : CollatzResearch.WordTrace tailWord_364087 prefixEnd_364087 27696537933869961724163 := by
  unfold tailWord_364087
  simp only [CollatzResearch.WordTrace]
  refine ⟨13279343831982454954218515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8852895887988303302812343 13279343831982454954218515)
  ·
    refine ⟨19919015747973682431327773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13279343831982454954218515 19919015747973682431327773)
    ·
      refine ⟨7469630905490130911747915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19919015747973682431327773 7469630905490130911747915)
      ·
        refine ⟨11204446358235196367621873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7469630905490130911747915 11204446358235196367621873)
        ·
          refine ⟨8403334768676397275716405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11204446358235196367621873 8403334768676397275716405)
          ·
            refine ⟨787812634563412244598413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8403334768676397275716405 787812634563412244598413)
            ·
              refine ⟨295429737961279591724405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 787812634563412244598413 295429737961279591724405)
              ·
                refine ⟨27696537933869961724163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 295429737961279591724405 27696537933869961724163)
                ·
                  rfl

theorem cell21_364087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3, 5].length) (baseStart_364087 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_364087 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_364087 prefixEnd_364087 := by exact prefixLift 364087
  have htrace : WordTrace (prefixWord ++ tailWord_364087) baseStart_364087 baseEnd_364087 := by
    simpa [prefixWord, tailWord_364087, baseEnd_364087] using wordTrace_append hprefix tailTrace_364087
  have hstable : (prefixWord ++ tailWord_364087).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364087).length < 2 ^ (prefixWord ++ tailWord_364087).sum := by decide
  have hdescent : baseEnd_364087 < baseStart_364087 := by decide
  rcases family_descends (prefixWord ++ tailWord_364087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364180 : List Nat := [2, 4, 2, 2, 2, 1, 2, 6]
def baseStart_364180 : Nat := 118140960795 + 364180 * 2 ^ 59
def prefixEnd_364180 : Nat := 4983230072969 + 3 ^ 40 * 364180 * 2
def baseEnd_364180 : Nat := 27703612556220796707433

theorem tailTrace_364180 : CollatzResearch.WordTrace tailWord_364180 prefixEnd_364180 27703612556220796707433 := by
  unfold tailWord_364180
  simp only [CollatzResearch.WordTrace]
  refine ⟨6641367910322765918676997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8855157213763687891569329 6641367910322765918676997)
  ·
    refine ⟨1245256483185518609751937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6641367910322765918676997 1245256483185518609751937)
    ·
      refine ⟨933942362389138957313953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1245256483185518609751937 933942362389138957313953)
      ·
        refine ⟨700456771791854217985465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 933942362389138957313953 700456771791854217985465)
        ·
          refine ⟨525342578843890663489099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 700456771791854217985465 525342578843890663489099)
          ·
            refine ⟨788013868265835995233649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 525342578843890663489099 788013868265835995233649)
            ·
              refine ⟨591010401199376996425237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 788013868265835995233649 591010401199376996425237)
              ·
                refine ⟨27703612556220796707433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 591010401199376996425237 27703612556220796707433)
                ·
                  rfl

theorem cell21_364180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 6].length) (baseStart_364180 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_364180 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_364180 prefixEnd_364180 := by exact prefixLift 364180
  have htrace : WordTrace (prefixWord ++ tailWord_364180) baseStart_364180 baseEnd_364180 := by
    simpa [prefixWord, tailWord_364180, baseEnd_364180] using wordTrace_append hprefix tailTrace_364180
  have hstable : (prefixWord ++ tailWord_364180).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364180).length < 2 ^ (prefixWord ++ tailWord_364180).sum := by decide
  have hdescent : baseEnd_364180 < baseStart_364180 := by decide
  rcases family_descends (prefixWord ++ tailWord_364180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364222 : List Nat := [4, 2, 1, 1, 2, 11]
def baseStart_364222 : Nat := 118140960795 + 364222 * 2 ^ 59
def prefixEnd_364222 : Nat := 4983230072969 + 3 ^ 40 * 364222 * 2
def baseEnd_364222 : Nat := 3078534171884431497119

theorem tailTrace_364222 : CollatzResearch.WordTrace tailWord_364222 prefixEnd_364222 3078534171884431497119 := by
  unfold tailWord_364222
  simp only [CollatzResearch.WordTrace]
  refine ⟨1660533460811671626297865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8856178457662248673588613 1660533460811671626297865)
  ·
    refine ⟨1245400095608753719723399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1660533460811671626297865 1245400095608753719723399)
    ·
      refine ⟨1868100143413130579585099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1245400095608753719723399 1868100143413130579585099)
      ·
        refine ⟨2802150215119695869377649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1868100143413130579585099 2802150215119695869377649)
        ·
          refine ⟨2101612661339771902033237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2802150215119695869377649 2101612661339771902033237)
          ·
            refine ⟨3078534171884431497119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2101612661339771902033237 3078534171884431497119)
            ·
              rfl

theorem cell21_364222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 11].length) (baseStart_364222 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_364222 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_364222 prefixEnd_364222 := by exact prefixLift 364222
  have htrace : WordTrace (prefixWord ++ tailWord_364222) baseStart_364222 baseEnd_364222 := by
    simpa [prefixWord, tailWord_364222, baseEnd_364222] using wordTrace_append hprefix tailTrace_364222
  have hstable : (prefixWord ++ tailWord_364222).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364222).length < 2 ^ (prefixWord ++ tailWord_364222).sum := by decide
  have hdescent : baseEnd_364222 < baseStart_364222 := by decide
  rcases family_descends (prefixWord ++ tailWord_364222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364346 : List Nat := [3, 1, 1, 1, 5, 3, 1, 1, 5]
def baseStart_364346 : Nat := 118140960795 + 364346 * 2 ^ 59
def prefixEnd_364346 : Nat := 4983230072969 + 3 ^ 40 * 364346 * 2
def baseEnd_364346 : Nat := 83148721130282990355293

theorem tailTrace_364346 : CollatzResearch.WordTrace tailWord_364346 prefixEnd_364346 83148721130282990355293 := by
  unfold tailWord_364346
  simp only [CollatzResearch.WordTrace]
  refine ⟨3322197584511035546974223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8859193558696094791931261 3322197584511035546974223)
  ·
    refine ⟨4983296376766553320461335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3322197584511035546974223 4983296376766553320461335)
    ·
      refine ⟨7474944565149829980692003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4983296376766553320461335 7474944565149829980692003)
      ·
        refine ⟨11212416847724744971038005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7474944565149829980692003 11212416847724744971038005)
        ·
          refine ⟨1051164079474194841034813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11212416847724744971038005 1051164079474194841034813)
          ·
            refine ⟨394186529802823065388055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1051164079474194841034813 394186529802823065388055)
            ·
              refine ⟨591279794704234598082083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 394186529802823065388055 591279794704234598082083)
              ·
                refine ⟨886919692056351897123125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 591279794704234598082083 886919692056351897123125)
                ·
                  refine ⟨83148721130282990355293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 886919692056351897123125 83148721130282990355293)
                  ·
                    rfl

theorem cell21_364346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 1, 5].length) (baseStart_364346 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_364346 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_364346 prefixEnd_364346 := by exact prefixLift 364346
  have htrace : WordTrace (prefixWord ++ tailWord_364346) baseStart_364346 baseEnd_364346 := by
    simpa [prefixWord, tailWord_364346, baseEnd_364346] using wordTrace_append hprefix tailTrace_364346
  have hstable : (prefixWord ++ tailWord_364346).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364346).length < 2 ^ (prefixWord ++ tailWord_364346).sum := by decide
  have hdescent : baseEnd_364346 < baseStart_364346 := by decide
  rcases family_descends (prefixWord ++ tailWord_364346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364360 : List Nat := [2, 1, 3, 1, 1, 5, 1, 3, 4]
def baseStart_364360 : Nat := 118140960795 + 364360 * 2 ^ 59
def prefixEnd_364360 : Nat := 4983230072969 + 3 ^ 40 * 364360 * 2
def baseEnd_364360 : Nat := 83151916121022077121931

theorem tailTrace_364360 : CollatzResearch.WordTrace tailWord_364360 prefixEnd_364360 83151916121022077121931 := by
  unfold tailWord_364360
  simp only [CollatzResearch.WordTrace]
  refine ⟨6644650479996711289453267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8859533973328948385937689 6644650479996711289453267)
  ·
    refine ⟨9966975719995066934179901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6644650479996711289453267 9966975719995066934179901)
    ·
      refine ⟨3737615894998150100317463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9966975719995066934179901 3737615894998150100317463)
      ·
        refine ⟨5606423842497225150476195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3737615894998150100317463 5606423842497225150476195)
        ·
          refine ⟨8409635763745837725714293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5606423842497225150476195 8409635763745837725714293)
          ·
            refine ⟨788403352851172286785715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8409635763745837725714293 788403352851172286785715)
            ·
              refine ⟨1182605029276758430178573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 788403352851172286785715 1182605029276758430178573)
              ·
                refine ⟨443476885978784411316965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1182605029276758430178573 443476885978784411316965)
                ·
                  refine ⟨83151916121022077121931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 443476885978784411316965 83151916121022077121931)
                  ·
                    rfl

theorem cell21_364360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 3, 4].length) (baseStart_364360 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_364360 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_364360 prefixEnd_364360 := by exact prefixLift 364360
  have htrace : WordTrace (prefixWord ++ tailWord_364360) baseStart_364360 baseEnd_364360 := by
    simpa [prefixWord, tailWord_364360, baseEnd_364360] using wordTrace_append hprefix tailTrace_364360
  have hstable : (prefixWord ++ tailWord_364360).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364360).length < 2 ^ (prefixWord ++ tailWord_364360).sum := by decide
  have hdescent : baseEnd_364360 < baseStart_364360 := by decide
  rcases family_descends (prefixWord ++ tailWord_364360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364394 : List Nat := [3, 1, 3, 4, 1, 1, 2, 2, 4]
def baseStart_364394 : Nat := 118140960795 + 364394 * 2 ^ 59
def prefixEnd_364394 : Nat := 4983230072969 + 3 ^ 40 * 364394 * 2
def baseEnd_364394 : Nat := 83159675384245573555195

theorem tailTrace_364394 : CollatzResearch.WordTrace tailWord_364394 prefixEnd_364394 83159675384245573555195 := by
  unfold tailWord_364394
  simp only [CollatzResearch.WordTrace]
  refine ⟨3322635260467561596411059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8860360694580164257096157 3322635260467561596411059)
  ·
    refine ⟨4983952890701342394616589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3322635260467561596411059 4983952890701342394616589)
    ·
      refine ⟨1868982334013003397981221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4983952890701342394616589 1868982334013003397981221)
      ·
        refine ⟨350434187627438137121479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1868982334013003397981221 350434187627438137121479)
        ·
          refine ⟨525651281441157205682219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 350434187627438137121479 525651281441157205682219)
          ·
            refine ⟨788476922161735808523329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 525651281441157205682219 788476922161735808523329)
            ·
              refine ⟨591357691621301856392497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 788476922161735808523329 591357691621301856392497)
              ·
                refine ⟨443518268715976392294373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 591357691621301856392497 443518268715976392294373)
                ·
                  refine ⟨83159675384245573555195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 443518268715976392294373 83159675384245573555195)
                  ·
                    rfl

theorem cell21_364394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 2, 4].length) (baseStart_364394 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_364394 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_364394 prefixEnd_364394 := by exact prefixLift 364394
  have htrace : WordTrace (prefixWord ++ tailWord_364394) baseStart_364394 baseEnd_364394 := by
    simpa [prefixWord, tailWord_364394, baseEnd_364394] using wordTrace_append hprefix tailTrace_364394
  have hstable : (prefixWord ++ tailWord_364394).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364394).length < 2 ^ (prefixWord ++ tailWord_364394).sum := by decide
  have hdescent : baseEnd_364394 < baseStart_364394 := by decide
  rcases family_descends (prefixWord ++ tailWord_364394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364405 : List Nat := [1, 3, 4, 1, 1, 1, 2, 3, 5]
def baseStart_364405 : Nat := 118140960795 + 364405 * 2 ^ 59
def prefixEnd_364405 : Nat := 4983230072969 + 3 ^ 40 * 364405 * 2
def baseEnd_364405 : Nat := 83162185734111998871839

theorem tailTrace_364405 : CollatzResearch.WordTrace tailWord_364405 prefixEnd_364405 83162185734111998871839 := by
  unfold tailWord_364405
  simp only [CollatzResearch.WordTrace]
  refine ⟨13290942244830395264294669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8860628163220263509529779 13290942244830395264294669)
  ·
    refine ⟨4984103341811398224110501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13290942244830395264294669 4984103341811398224110501)
    ·
      refine ⟨934519376589637167020719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4984103341811398224110501 934519376589637167020719)
      ·
        refine ⟨1401779064884455750531079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 934519376589637167020719 1401779064884455750531079)
        ·
          refine ⟨2102668597326683625796619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1401779064884455750531079 2102668597326683625796619)
          ·
            refine ⟨3154002895990025438694929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2102668597326683625796619 3154002895990025438694929)
            ·
              refine ⟨2365502171992519079021197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3154002895990025438694929 2365502171992519079021197)
              ·
                refine ⟨887063314497194654632949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2365502171992519079021197 887063314497194654632949)
                ·
                  refine ⟨83162185734111998871839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 887063314497194654632949 83162185734111998871839)
                  ·
                    rfl

theorem cell21_364405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 3, 5].length) (baseStart_364405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_364405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_364405 prefixEnd_364405 := by exact prefixLift 364405
  have htrace : WordTrace (prefixWord ++ tailWord_364405) baseStart_364405 baseEnd_364405 := by
    simpa [prefixWord, tailWord_364405, baseEnd_364405] using wordTrace_append hprefix tailTrace_364405
  have hstable : (prefixWord ++ tailWord_364405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364405).length < 2 ^ (prefixWord ++ tailWord_364405).sum := by decide
  have hdescent : baseEnd_364405 < baseStart_364405 := by decide
  rcases family_descends (prefixWord ++ tailWord_364405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364433 : List Nat := [1, 2, 2, 1, 1, 1, 4, 9]
def baseStart_364433 : Nat := 118140960795 + 364433 * 2 ^ 59
def prefixEnd_364433 : Nat := 4983230072969 + 3 ^ 40 * 364433 * 2
def baseEnd_364433 : Nat := 27722858571863390801705

theorem tailTrace_364433 : CollatzResearch.WordTrace tailWord_364433 prefixEnd_364433 27722858571863390801705 := by
  unfold tailWord_364433
  simp only [CollatzResearch.WordTrace]
  refine ⟨13291963488728956046313953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8861308992485970697542635 13291963488728956046313953)
  ·
    refine ⟨9968972616546717034735465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13291963488728956046313953 9968972616546717034735465)
    ·
      refine ⟨7476729462410037776051599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9968972616546717034735465 7476729462410037776051599)
      ·
        refine ⟨11215094193615056664077399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7476729462410037776051599 11215094193615056664077399)
        ·
          refine ⟨16822641290422584996116099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11215094193615056664077399 16822641290422584996116099)
          ·
            refine ⟨25233961935633877494174149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16822641290422584996116099 25233961935633877494174149)
            ·
              refine ⟨4731367862931352030157653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25233961935633877494174149 4731367862931352030157653)
              ·
                refine ⟨27722858571863390801705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4731367862931352030157653 27722858571863390801705)
                ·
                  rfl

theorem cell21_364433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 9].length) (baseStart_364433 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_364433 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_364433 prefixEnd_364433 := by exact prefixLift 364433
  have htrace : WordTrace (prefixWord ++ tailWord_364433) baseStart_364433 baseEnd_364433 := by
    simpa [prefixWord, tailWord_364433, baseEnd_364433] using wordTrace_append hprefix tailTrace_364433
  have hstable : (prefixWord ++ tailWord_364433).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364433).length < 2 ^ (prefixWord ++ tailWord_364433).sum := by decide
  have hdescent : baseEnd_364433 < baseStart_364433 := by decide
  rcases family_descends (prefixWord ++ tailWord_364433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364515 : List Nat := [1, 1, 1, 6, 1, 3, 3, 2, 3]
def baseStart_364515 : Nat := 118140960795 + 364515 * 2 ^ 59
def prefixEnd_364515 : Nat := 4983230072969 + 3 ^ 40 * 364515 * 2
def baseEnd_364515 : Nat := 83187289232776252038281

theorem tailTrace_364515 : CollatzResearch.WordTrace tailWord_364515 prefixEnd_364515 83187289232776252038281 := by
  unfold tailWord_364515
  simp only [CollatzResearch.WordTrace]
  refine ⟨13294954274431884050798999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8863302849621256033865999 13294954274431884050798999)
  ·
    refine ⟨19942431411647826076198499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13294954274431884050798999 19942431411647826076198499)
    ·
      refine ⟨29913647117471739114297749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19942431411647826076198499 29913647117471739114297749)
      ·
        refine ⟨1402202208631487770982707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 29913647117471739114297749 1402202208631487770982707)
        ·
          refine ⟨2103303312947231656474061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1402202208631487770982707 2103303312947231656474061)
          ·
            refine ⟨788738742355211871177773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2103303312947231656474061 788738742355211871177773)
            ·
              refine ⟨295777028383204451691665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 788738742355211871177773 295777028383204451691665)
              ·
                refine ⟨221832771287403338768749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 295777028383204451691665 221832771287403338768749)
                ·
                  refine ⟨83187289232776252038281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 221832771287403338768749 83187289232776252038281)
                  ·
                    rfl

theorem cell21_364515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3, 2, 3].length) (baseStart_364515 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_364515 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_364515 prefixEnd_364515 := by exact prefixLift 364515
  have htrace : WordTrace (prefixWord ++ tailWord_364515) baseStart_364515 baseEnd_364515 := by
    simpa [prefixWord, tailWord_364515, baseEnd_364515] using wordTrace_append hprefix tailTrace_364515
  have hstable : (prefixWord ++ tailWord_364515).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364515).length < 2 ^ (prefixWord ++ tailWord_364515).sum := by decide
  have hdescent : baseEnd_364515 < baseStart_364515 := by decide
  rcases family_descends (prefixWord ++ tailWord_364515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364526 : List Nat := [4, 1, 2, 1, 3, 1, 1, 8]
def baseStart_364526 : Nat := 118140960795 + 364526 * 2 ^ 59
def prefixEnd_364526 : Nat := 4983230072969 + 3 ^ 40 * 364526 * 2
def baseEnd_364526 : Nat := 27729933194214225784975

theorem tailTrace_364526 : CollatzResearch.WordTrace tailWord_364526 prefixEnd_364526 27729933194214225784975 := by
  unfold tailWord_364526
  simp only [CollatzResearch.WordTrace]
  refine ⟨1661919434674004116181179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8863570318261355286299621 1661919434674004116181179)
  ·
    refine ⟨2492879152011006174271769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1661919434674004116181179 2492879152011006174271769)
    ·
      refine ⟨1869659364008254630703827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2492879152011006174271769 1869659364008254630703827)
      ·
        refine ⟨2804489046012381946055741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1869659364008254630703827 2804489046012381946055741)
        ·
          refine ⟨1051683392254643229770903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2804489046012381946055741 1051683392254643229770903)
          ·
            refine ⟨1577525088381964844656355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1051683392254643229770903 1577525088381964844656355)
            ·
              refine ⟨2366287632572947266984533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1577525088381964844656355 2366287632572947266984533)
              ·
                refine ⟨27729933194214225784975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2366287632572947266984533 27729933194214225784975)
                ·
                  rfl

theorem cell21_364526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 8].length) (baseStart_364526 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_364526 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_364526 prefixEnd_364526 := by exact prefixLift 364526
  have htrace : WordTrace (prefixWord ++ tailWord_364526) baseStart_364526 baseEnd_364526 := by
    simpa [prefixWord, tailWord_364526, baseEnd_364526] using wordTrace_append hprefix tailTrace_364526
  have hstable : (prefixWord ++ tailWord_364526).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364526).length < 2 ^ (prefixWord ++ tailWord_364526).sum := by decide
  have hdescent : baseEnd_364526 < baseStart_364526 := by decide
  rcases family_descends (prefixWord ++ tailWord_364526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364540 : List Nat := [2, 2, 2, 1, 2, 2, 2, 1, 7]
def baseStart_364540 : Nat := 118140960795 + 364540 * 2 ^ 59
def prefixEnd_364540 : Nat := 4983230072969 + 3 ^ 40 * 364540 * 2
def baseEnd_364540 : Nat := 83192994573381764121563

theorem tailTrace_364540 : CollatzResearch.WordTrace tailWord_364540 prefixEnd_364540 83192994573381764121563 := by
  unfold tailWord_364540
  simp only [CollatzResearch.WordTrace]
  refine ⟨6647933049670656660229537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8863910732894208880306049 6647933049670656660229537)
  ·
    refine ⟨4985949787252992495172153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6647933049670656660229537 4985949787252992495172153)
    ·
      refine ⟨3739462340439744371379115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4985949787252992495172153 3739462340439744371379115)
      ·
        refine ⟨5609193510659616557068673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3739462340439744371379115 5609193510659616557068673)
        ·
          refine ⟨4206895132994712417801505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5609193510659616557068673 4206895132994712417801505)
          ·
            refine ⟨3155171349746034313351129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4206895132994712417801505 3155171349746034313351129)
            ·
              refine ⟨2366378512309525735013347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3155171349746034313351129 2366378512309525735013347)
              ·
                refine ⟨3549567768464288602520021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2366378512309525735013347 3549567768464288602520021)
                ·
                  refine ⟨83192994573381764121563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3549567768464288602520021 83192994573381764121563)
                  ·
                    rfl

theorem cell21_364540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 7].length) (baseStart_364540 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_364540 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_364540 prefixEnd_364540 := by exact prefixLift 364540
  have htrace : WordTrace (prefixWord ++ tailWord_364540) baseStart_364540 baseEnd_364540 := by
    simpa [prefixWord, tailWord_364540, baseEnd_364540] using wordTrace_append hprefix tailTrace_364540
  have hstable : (prefixWord ++ tailWord_364540).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364540).length < 2 ^ (prefixWord ++ tailWord_364540).sum := by decide
  have hdescent : baseEnd_364540 < baseStart_364540 := by decide
  rcases family_descends (prefixWord ++ tailWord_364540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364633 : List Nat := [1, 2, 1, 2, 2, 1, 3, 6, 3]
def baseStart_364633 : Nat := 118140960795 + 364633 * 2 ^ 59
def prefixEnd_364633 : Nat := 4983230072969 + 3 ^ 40 * 364633 * 2
def baseEnd_364633 : Nat := 83214218440434269071373

theorem tailTrace_364633 : CollatzResearch.WordTrace tailWord_364633 prefixEnd_364633 83214218440434269071373 := by
  unfold tailWord_364633
  simp only [CollatzResearch.WordTrace]
  refine ⟨13299258088004390203594553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8866172058669593469063035 13299258088004390203594553)
  ·
    refine ⟨9974443566003292652695915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13299258088004390203594553 9974443566003292652695915)
    ·
      refine ⟨14961665349004938979043873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9974443566003292652695915 14961665349004938979043873)
      ·
        refine ⟨11221249011753704234282905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14961665349004938979043873 11221249011753704234282905)
        ·
          refine ⟨8415936758815278175712179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11221249011753704234282905 8415936758815278175712179)
          ·
            refine ⟨12623905138222917263568269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8415936758815278175712179 12623905138222917263568269)
            ·
              refine ⟨4733964426833593973838101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12623905138222917263568269 4733964426833593973838101)
              ·
                refine ⟨221904582507824717523661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4733964426833593973838101 221904582507824717523661)
                ·
                  refine ⟨83214218440434269071373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 221904582507824717523661 83214218440434269071373)
                  ·
                    rfl

theorem cell21_364633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 6, 3].length) (baseStart_364633 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_364633 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_364633 prefixEnd_364633 := by exact prefixLift 364633
  have htrace : WordTrace (prefixWord ++ tailWord_364633) baseStart_364633 baseEnd_364633 := by
    simpa [prefixWord, tailWord_364633, baseEnd_364633] using wordTrace_append hprefix tailTrace_364633
  have hstable : (prefixWord ++ tailWord_364633).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364633).length < 2 ^ (prefixWord ++ tailWord_364633).sum := by decide
  have hdescent : baseEnd_364633 < baseStart_364633 := by decide
  rcases family_descends (prefixWord ++ tailWord_364633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364698 : List Nat := [3, 1, 1, 5, 2, 2, 2, 1, 4]
def baseStart_364698 : Nat := 118140960795 + 364698 * 2 ^ 59
def prefixEnd_364698 : Nat := 4983230072969 + 3 ^ 40 * 364698 * 2
def baseEnd_364698 : Nat := 83229052326008600487907

theorem tailTrace_364698 : CollatzResearch.WordTrace tailWord_364698 prefixEnd_364698 83229052326008600487907 := by
  unfold tailWord_364698
  simp only [CollatzResearch.WordTrace]
  refine ⟨3325407208192226576177687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8867752555179270869807165 3325407208192226576177687)
  ·
    refine ⟨4988110812288339864266531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3325407208192226576177687 4988110812288339864266531)
    ·
      refine ⟨7482166218432509796399797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4988110812288339864266531 7482166218432509796399797)
      ·
        refine ⟨701453082978047793412481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7482166218432509796399797 701453082978047793412481)
        ·
          refine ⟨526089812233535845059361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 701453082978047793412481 526089812233535845059361)
          ·
            refine ⟨394567359175151883794521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 526089812233535845059361 394567359175151883794521)
            ·
              refine ⟨295925519381363912845891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 394567359175151883794521 295925519381363912845891)
              ·
                refine ⟨443888279072045869268837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 295925519381363912845891 443888279072045869268837)
                ·
                  refine ⟨83229052326008600487907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 443888279072045869268837 83229052326008600487907)
                  ·
                    rfl

theorem cell21_364698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2, 1, 4].length) (baseStart_364698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_364698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_364698 prefixEnd_364698 := by exact prefixLift 364698
  have htrace : WordTrace (prefixWord ++ tailWord_364698) baseStart_364698 baseEnd_364698 := by
    simpa [prefixWord, tailWord_364698, baseEnd_364698] using wordTrace_append hprefix tailTrace_364698
  have hstable : (prefixWord ++ tailWord_364698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364698).length < 2 ^ (prefixWord ++ tailWord_364698).sum := by decide
  have hdescent : baseEnd_364698 < baseStart_364698 := by decide
  rcases family_descends (prefixWord ++ tailWord_364698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364740 : List Nat := [2, 3, 3, 1, 2, 1, 1, 4, 4]
def baseStart_364740 : Nat := 118140960795 + 364740 * 2 ^ 59
def prefixEnd_364740 : Nat := 4983230072969 + 3 ^ 40 * 364740 * 2
def baseEnd_364740 : Nat := 83238637298225860787821

theorem tailTrace_364740 : CollatzResearch.WordTrace tailWord_364740 prefixEnd_364740 83238637298225860787821 := by
  unfold tailWord_364740
  simp only [CollatzResearch.WordTrace]
  refine ⟨6651580349308373738869837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8868773799077831651826449 6651580349308373738869837)
  ·
    refine ⟨2494342630990640152076189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6651580349308373738869837 2494342630990640152076189)
    ·
      refine ⟨935378486621490057028571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2494342630990640152076189 935378486621490057028571)
      ·
        refine ⟨1403067729932235085542857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 935378486621490057028571 1403067729932235085542857)
        ·
          refine ⟨1052300797449176314157143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1403067729932235085542857 1052300797449176314157143)
          ·
            refine ⟨1578451196173764471235715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1052300797449176314157143 1578451196173764471235715)
            ·
              refine ⟨2367676794260646706853573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1578451196173764471235715 2367676794260646706853573)
              ·
                refine ⟨443939398923871257535045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2367676794260646706853573 443939398923871257535045)
                ·
                  refine ⟨83238637298225860787821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 443939398923871257535045 83238637298225860787821)
                  ·
                    rfl

theorem cell21_364740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_364740 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_364740 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_364740 prefixEnd_364740 := by exact prefixLift 364740
  have htrace : WordTrace (prefixWord ++ tailWord_364740) baseStart_364740 baseEnd_364740 := by
    simpa [prefixWord, tailWord_364740, baseEnd_364740] using wordTrace_append hprefix tailTrace_364740
  have hstable : (prefixWord ++ tailWord_364740).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364740).length < 2 ^ (prefixWord ++ tailWord_364740).sum := by decide
  have hdescent : baseEnd_364740 < baseStart_364740 := by decide
  rcases family_descends (prefixWord ++ tailWord_364740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364754 : List Nat := [3, 2, 2, 2, 1, 2, 3, 6]
def baseStart_364754 : Nat := 118140960795 + 364754 * 2 ^ 59
def prefixEnd_364754 : Nat := 4983230072969 + 3 ^ 40 * 364754 * 2
def baseEnd_364754 : Nat := 27747277429654982518153

theorem tailTrace_364754 : CollatzResearch.WordTrace tailWord_364754 prefixEnd_364754 27747277429654982518153 := by
  unfold tailWord_364754
  simp only [CollatzResearch.WordTrace]
  refine ⟨3325917830141506967187329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8869114213710685245832877 3325917830141506967187329)
  ·
    refine ⟨2494438372606130225390497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3325917830141506967187329 2494438372606130225390497)
    ·
      refine ⟨1870828779454597669042873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2494438372606130225390497 1870828779454597669042873)
      ·
        refine ⟨1403121584590948251782155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1870828779454597669042873 1403121584590948251782155)
        ·
          refine ⟨2104682376886422377673233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1403121584590948251782155 2104682376886422377673233)
          ·
            refine ⟨1578511782664816783254925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2104682376886422377673233 1578511782664816783254925)
            ·
              refine ⟨591941918499306293720597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1578511782664816783254925 591941918499306293720597)
              ·
                refine ⟨27747277429654982518153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 591941918499306293720597 27747277429654982518153)
                ·
                  rfl

theorem cell21_364754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 6].length) (baseStart_364754 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_364754 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_364754 prefixEnd_364754 := by exact prefixLift 364754
  have htrace : WordTrace (prefixWord ++ tailWord_364754) baseStart_364754 baseEnd_364754 := by
    simpa [prefixWord, tailWord_364754, baseEnd_364754] using wordTrace_append hprefix tailTrace_364754
  have hstable : (prefixWord ++ tailWord_364754).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364754).length < 2 ^ (prefixWord ++ tailWord_364754).sum := by decide
  have hdescent : baseEnd_364754 < baseStart_364754 := by decide
  rcases family_descends (prefixWord ++ tailWord_364754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364768 : List Nat := [2, 1, 1, 3, 1, 3, 3, 2, 5]
def baseStart_364768 : Nat := 118140960795 + 364768 * 2 ^ 59
def prefixEnd_364768 : Nat := 4983230072969 + 3 ^ 40 * 364768 * 2
def baseEnd_364768 : Nat := 83245027279704034321097

theorem tailTrace_364768 : CollatzResearch.WordTrace tailWord_364768 prefixEnd_364768 83245027279704034321097 := by
  unfold tailWord_364768
  simp only [CollatzResearch.WordTrace]
  refine ⟨6652090971257654129879479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8869454628343538839839305 6652090971257654129879479)
  ·
    refine ⟨9978136456886481194819219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6652090971257654129879479 9978136456886481194819219)
    ·
      refine ⟨14967204685329721792228829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9978136456886481194819219 14967204685329721792228829)
      ·
        refine ⟨5612701756998645672085811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14967204685329721792228829 5612701756998645672085811)
        ·
          refine ⟨8419052635497968508128717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5612701756998645672085811 8419052635497968508128717)
          ·
            refine ⟨3157144738311738190548269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8419052635497968508128717 3157144738311738190548269)
            ·
              refine ⟨1183929276866901821455601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3157144738311738190548269 1183929276866901821455601)
              ·
                refine ⟨887946957650176366091701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1183929276866901821455601 887946957650176366091701)
                ·
                  refine ⟨83245027279704034321097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 887946957650176366091701 83245027279704034321097)
                  ·
                    rfl

theorem cell21_364768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 2, 5].length) (baseStart_364768 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_364768 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_364768 prefixEnd_364768 := by exact prefixLift 364768
  have htrace : WordTrace (prefixWord ++ tailWord_364768) baseStart_364768 baseEnd_364768 := by
    simpa [prefixWord, tailWord_364768, baseEnd_364768] using wordTrace_append hprefix tailTrace_364768
  have hstable : (prefixWord ++ tailWord_364768).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364768).length < 2 ^ (prefixWord ++ tailWord_364768).sum := by decide
  have hdescent : baseEnd_364768 < baseStart_364768 := by decide
  rcases family_descends (prefixWord ++ tailWord_364768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364785 : List Nat := [1, 2, 2, 2, 2, 1, 3, 5, 3]
def baseStart_364785 : Nat := 118140960795 + 364785 * 2 ^ 59
def prefixEnd_364785 : Nat := 4983230072969 + 3 ^ 40 * 364785 * 2
def baseEnd_364785 : Nat := 83248906911315782537729

theorem tailTrace_364785 : CollatzResearch.WordTrace tailWord_364785 prefixEnd_364785 83248906911315782537729 := by
  unfold tailWord_364785
  simp only [CollatzResearch.WordTrace]
  refine ⟨13304801983453720163127809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8869867988969146775418539 13304801983453720163127809)
  ·
    refine ⟨9978601487590290122345857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13304801983453720163127809 9978601487590290122345857)
    ·
      refine ⟨7483951115692717591759393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9978601487590290122345857 7483951115692717591759393)
      ·
        refine ⟨5612963336769538193819545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7483951115692717591759393 5612963336769538193819545)
        ·
          refine ⟨4209722502577153645364659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5612963336769538193819545 4209722502577153645364659)
          ·
            refine ⟨6314583753865730468046989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4209722502577153645364659 6314583753865730468046989)
            ·
              refine ⟨2367968907699648925517621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6314583753865730468046989 2367968907699648925517621)
              ·
                refine ⟨221997085096842086767277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2367968907699648925517621 221997085096842086767277)
                ·
                  refine ⟨83248906911315782537729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 221997085096842086767277 83248906911315782537729)
                  ·
                    rfl

theorem cell21_364785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 5, 3].length) (baseStart_364785 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_364785 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_364785 prefixEnd_364785 := by exact prefixLift 364785
  have htrace : WordTrace (prefixWord ++ tailWord_364785) baseStart_364785 baseEnd_364785 := by
    simpa [prefixWord, tailWord_364785, baseEnd_364785] using wordTrace_append hprefix tailTrace_364785
  have hstable : (prefixWord ++ tailWord_364785).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364785).length < 2 ^ (prefixWord ++ tailWord_364785).sum := by decide
  have hdescent : baseEnd_364785 < baseStart_364785 := by decide
  rcases family_descends (prefixWord ++ tailWord_364785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364802 : List Nat := [3, 4, 1, 1, 2, 2, 2, 1, 5]
def baseStart_364802 : Nat := 118140960795 + 364802 * 2 ^ 59
def prefixEnd_364802 : Nat := 4983230072969 + 3 ^ 40 * 364802 * 2
def baseEnd_364802 : Nat := 83252786542927530754361

theorem tailTrace_364802 : CollatzResearch.WordTrace tailWord_364802 prefixEnd_364802 83252786542927530754361 := by
  unfold tailWord_364802
  simp only [CollatzResearch.WordTrace]
  refine ⟨3326355506098033016624165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8870281349594754710997773 3326355506098033016624165)
  ·
    refine ⟨623691657393381190617031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3326355506098033016624165 623691657393381190617031)
    ·
      refine ⟨935537486090071785925547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 623691657393381190617031 935537486090071785925547)
      ·
        refine ⟨1403306229135107678888321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 935537486090071785925547 1403306229135107678888321)
        ·
          refine ⟨1052479671851330759166241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1403306229135107678888321 1052479671851330759166241)
          ·
            refine ⟨789359753888498069374681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1052479671851330759166241 789359753888498069374681)
            ·
              refine ⟨592019815416373552031011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 789359753888498069374681 592019815416373552031011)
              ·
                refine ⟨888029723124560328046517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 592019815416373552031011 888029723124560328046517)
                ·
                  refine ⟨83252786542927530754361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 888029723124560328046517 83252786542927530754361)
                  ·
                    rfl

theorem cell21_364802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_364802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_364802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_364802 prefixEnd_364802 := by exact prefixLift 364802
  have htrace : WordTrace (prefixWord ++ tailWord_364802) baseStart_364802 baseEnd_364802 := by
    simpa [prefixWord, tailWord_364802, baseEnd_364802] using wordTrace_append hprefix tailTrace_364802
  have hstable : (prefixWord ++ tailWord_364802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364802).length < 2 ^ (prefixWord ++ tailWord_364802).sum := by decide
  have hdescent : baseEnd_364802 < baseStart_364802 := by decide
  rcases family_descends (prefixWord ++ tailWord_364802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364954 : List Nat := [3, 1, 1, 4, 1, 3, 2, 3, 3]
def baseStart_364954 : Nat := 118140960795 + 364954 * 2 ^ 59
def prefixEnd_364954 : Nat := 4983230072969 + 3 ^ 40 * 364954 * 2
def baseEnd_364954 : Nat := 83287475013809044220717

theorem tailTrace_364954 : CollatzResearch.WordTrace tailWord_364954 prefixEnd_364954 83287475013809044220717 := by
  unfold tailWord_364954
  simp only [CollatzResearch.WordTrace]
  refine ⟨3327741479960365506507479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8873977279894308017353277 3327741479960365506507479)
  ·
    refine ⟨4991612219940548259761219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3327741479960365506507479 4991612219940548259761219)
    ·
      refine ⟨7487418329910822389641829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4991612219940548259761219 7487418329910822389641829)
      ·
        refine ⟨1403890936858279198057843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7487418329910822389641829 1403890936858279198057843)
        ·
          refine ⟨2105836405287418797086765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1403890936858279198057843 2105836405287418797086765)
          ·
            refine ⟨789688651982782048907537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2105836405287418797086765 789688651982782048907537)
            ·
              refine ⟨592266488987086536680653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 789688651982782048907537 592266488987086536680653)
              ·
                refine ⟨222099933370157451255245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 592266488987086536680653 222099933370157451255245)
                ·
                  refine ⟨83287475013809044220717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 222099933370157451255245 83287475013809044220717)
                  ·
                    rfl

theorem cell21_364954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 3, 3].length) (baseStart_364954 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_364954 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_364954 prefixEnd_364954 := by exact prefixLift 364954
  have htrace : WordTrace (prefixWord ++ tailWord_364954) baseStart_364954 baseEnd_364954 := by
    simpa [prefixWord, tailWord_364954, baseEnd_364954] using wordTrace_append hprefix tailTrace_364954
  have hstable : (prefixWord ++ tailWord_364954).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364954).length < 2 ^ (prefixWord ++ tailWord_364954).sum := by decide
  have hdescent : baseEnd_364954 < baseStart_364954 := by decide
  rcases family_descends (prefixWord ++ tailWord_364954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364968 : List Nat := [2, 1, 6, 1, 1, 2, 1, 1, 6]
def baseStart_364968 : Nat := 118140960795 + 364968 * 2 ^ 59
def prefixEnd_364968 : Nat := 4983230072969 + 3 ^ 40 * 364968 * 2
def baseEnd_364968 : Nat := 83290670004548130987355

theorem tailTrace_364968 : CollatzResearch.WordTrace tailWord_364968 prefixEnd_364968 83290670004548130987355 := by
  unfold tailWord_364968
  simp only [CollatzResearch.WordTrace]
  refine ⟨6655738270895371208519779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8874317694527161611359705 6655738270895371208519779)
  ·
    refine ⟨9983607406343056812779669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6655738270895371208519779 9983607406343056812779669)
    ·
      refine ⟨467981597172330788099047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9983607406343056812779669 467981597172330788099047)
      ·
        refine ⟨701972395758496182148571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 467981597172330788099047 701972395758496182148571)
        ·
          refine ⟨1052958593637744273222857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 701972395758496182148571 1052958593637744273222857)
          ·
            refine ⟨789718945228308204917143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1052958593637744273222857 789718945228308204917143)
            ·
              refine ⟨1184578417842462307375715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 789718945228308204917143 1184578417842462307375715)
              ·
                refine ⟨1776867626763693461063573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1184578417842462307375715 1776867626763693461063573)
                ·
                  refine ⟨83290670004548130987355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1776867626763693461063573 83290670004548130987355)
                  ·
                    rfl

theorem cell21_364968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 6].length) (baseStart_364968 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_364968 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_364968 prefixEnd_364968 := by exact prefixLift 364968
  have htrace : WordTrace (prefixWord ++ tailWord_364968) baseStart_364968 baseEnd_364968 := by
    simpa [prefixWord, tailWord_364968, baseEnd_364968] using wordTrace_append hprefix tailTrace_364968
  have hstable : (prefixWord ++ tailWord_364968).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364968).length < 2 ^ (prefixWord ++ tailWord_364968).sum := by decide
  have hdescent : baseEnd_364968 < baseStart_364968 := by decide
  rcases family_descends (prefixWord ++ tailWord_364968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365041 : List Nat := [1, 2, 2, 2, 3, 1, 4, 6]
def baseStart_365041 : Nat := 118140960795 + 365041 * 2 ^ 59
def prefixEnd_365041 : Nat := 4983230072969 + 3 ^ 40 * 365041 * 2
def baseEnd_365041 : Nat := 27769109866372075423513

theorem tailTrace_365041 : CollatzResearch.WordTrace tailWord_365041 prefixEnd_365041 27769109866372075423513 := by
  unfold tailWord_365041
  simp only [CollatzResearch.WordTrace]
  refine ⟨13314139070526275884446977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8876092713684183922964651 13314139070526275884446977)
  ·
    refine ⟨9985604302894706913335233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13314139070526275884446977 9985604302894706913335233)
    ·
      refine ⟨7489203227171030185001425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9985604302894706913335233 7489203227171030185001425)
      ·
        refine ⟨5616902420378272638751069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7489203227171030185001425 5616902420378272638751069)
        ·
          refine ⟨2106338407641852239531651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5616902420378272638751069 2106338407641852239531651)
          ·
            refine ⟨3159507611462778359297477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2106338407641852239531651 3159507611462778359297477)
            ·
              refine ⟨592407677149270942368277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3159507611462778359297477 592407677149270942368277)
              ·
                refine ⟨27769109866372075423513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 592407677149270942368277 27769109866372075423513)
                ·
                  rfl

theorem cell21_365041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 6].length) (baseStart_365041 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_365041 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_365041 prefixEnd_365041 := by exact prefixLift 365041
  have htrace : WordTrace (prefixWord ++ tailWord_365041) baseStart_365041 baseEnd_365041 := by
    simpa [prefixWord, tailWord_365041, baseEnd_365041] using wordTrace_append hprefix tailTrace_365041
  have hstable : (prefixWord ++ tailWord_365041).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365041).length < 2 ^ (prefixWord ++ tailWord_365041).sum := by decide
  have hdescent : baseEnd_365041 < baseStart_365041 := by decide
  rcases family_descends (prefixWord ++ tailWord_365041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365055 : List Nat := [1, 1, 2, 2, 1, 2, 4, 1, 7]
def baseStart_365055 : Nat := 118140960795 + 365055 * 2 ^ 59
def prefixEnd_365055 : Nat := 4983230072969 + 3 ^ 40 * 365055 * 2
def baseEnd_365055 : Nat := 83310524589855313037177

theorem tailTrace_365055 : CollatzResearch.WordTrace tailWord_365055 prefixEnd_365055 83310524589855313037177 := by
  unfold tailWord_365055
  simp only [CollatzResearch.WordTrace]
  refine ⟨13314649692475556275456619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8876433128317037516971079 13314649692475556275456619)
  ·
    refine ⟨19971974538713334413184929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13314649692475556275456619 19971974538713334413184929)
    ·
      refine ⟨14978980904035000809888697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19971974538713334413184929 14978980904035000809888697)
      ·
        refine ⟨11234235678026250607416523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14978980904035000809888697 11234235678026250607416523)
        ·
          refine ⟨16851353517039375911124785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11234235678026250607416523 16851353517039375911124785)
          ·
            refine ⟨12638515137779531933343589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16851353517039375911124785 12638515137779531933343589)
            ·
              refine ⟨2369721588333662237501923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12638515137779531933343589 2369721588333662237501923)
              ·
                refine ⟨3554582382500493356252885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2369721588333662237501923 3554582382500493356252885)
                ·
                  refine ⟨83310524589855313037177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3554582382500493356252885 83310524589855313037177)
                  ·
                    rfl

theorem cell21_365055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 7].length) (baseStart_365055 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_365055 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_365055 prefixEnd_365055 := by exact prefixLift 365055
  have htrace : WordTrace (prefixWord ++ tailWord_365055) baseStart_365055 baseEnd_365055 := by
    simpa [prefixWord, tailWord_365055, baseEnd_365055] using wordTrace_append hprefix tailTrace_365055
  have hstable : (prefixWord ++ tailWord_365055).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365055).length < 2 ^ (prefixWord ++ tailWord_365055).sum := by decide
  have hdescent : baseEnd_365055 < baseStart_365055 := by decide
  rcases family_descends (prefixWord ++ tailWord_365055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365089 : List Nat := [1, 2, 3, 2, 2, 1, 3, 4, 3]
def baseStart_365089 : Nat := 118140960795 + 365089 * 2 ^ 59
def prefixEnd_365089 : Nat := 4983230072969 + 3 ^ 40 * 365089 * 2
def baseEnd_365089 : Nat := 83318283853078809470441

theorem tailTrace_365089 : CollatzResearch.WordTrace tailWord_365089 prefixEnd_365089 83318283853078809470441 := by
  unfold tailWord_365089
  simp only [CollatzResearch.WordTrace]
  refine ⟨13315889774352380082194321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8877259849568253388129547 13315889774352380082194321)
  ·
    refine ⟨9986917330764285061645741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13315889774352380082194321 9986917330764285061645741)
    ·
      refine ⟨3745093999036606898117153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9986917330764285061645741 3745093999036606898117153)
      ·
        refine ⟨2808820499277455173587865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3745093999036606898117153 2808820499277455173587865)
        ·
          refine ⟨2106615374458091380190899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2808820499277455173587865 2106615374458091380190899)
          ·
            refine ⟨3159923061687137070286349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2106615374458091380190899 3159923061687137070286349)
            ·
              refine ⟨1184971148132676401357381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3159923061687137070286349 1184971148132676401357381)
              ·
                refine ⟨222182090274876825254509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1184971148132676401357381 222182090274876825254509)
                ·
                  refine ⟨83318283853078809470441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 222182090274876825254509 83318283853078809470441)
                  ·
                    rfl

theorem cell21_365089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 4, 3].length) (baseStart_365089 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_365089 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_365089 prefixEnd_365089 := by exact prefixLift 365089
  have htrace : WordTrace (prefixWord ++ tailWord_365089) baseStart_365089 baseEnd_365089 := by
    simpa [prefixWord, tailWord_365089, baseEnd_365089] using wordTrace_append hprefix tailTrace_365089
  have hstable : (prefixWord ++ tailWord_365089).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365089).length < 2 ^ (prefixWord ++ tailWord_365089).sum := by decide
  have hdescent : baseEnd_365089 < baseStart_365089 := by decide
  rcases family_descends (prefixWord ++ tailWord_365089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365092 : List Nat := [2, 3, 1, 5, 2, 1, 1, 6]
def baseStart_365092 : Nat := 118140960795 + 365092 * 2 ^ 59
def prefixEnd_365092 : Nat := 4983230072969 + 3 ^ 40 * 365092 * 2
def baseEnd_365092 : Nat := 27772989497983823640145

theorem tailTrace_365092 : CollatzResearch.WordTrace tailWord_365092 prefixEnd_365092 27772989497983823640145 := by
  unfold tailWord_365092
  simp only [CollatzResearch.WordTrace]
  refine ⟨6657999596670755797276765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8877332795561007729702353 6657999596670755797276765)
  ·
    refine ⟨2496749848751533423978787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6657999596670755797276765 2496749848751533423978787)
    ·
      refine ⟨3745124773127300135968181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2496749848751533423978787 3745124773127300135968181)
      ·
        refine ⟨351105447480684387747017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3745124773127300135968181 351105447480684387747017)
        ·
          refine ⟨263329085610513290810263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 351105447480684387747017 263329085610513290810263)
          ·
            refine ⟨394993628415769936215395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263329085610513290810263 394993628415769936215395)
            ·
              refine ⟨592490442623654904323093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 394993628415769936215395 592490442623654904323093)
              ·
                refine ⟨27772989497983823640145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 592490442623654904323093 27772989497983823640145)
                ·
                  rfl

theorem cell21_365092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 6].length) (baseStart_365092 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_365092 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_365092 prefixEnd_365092 := by exact prefixLift 365092
  have htrace : WordTrace (prefixWord ++ tailWord_365092) baseStart_365092 baseEnd_365092 := by
    simpa [prefixWord, tailWord_365092, baseEnd_365092] using wordTrace_append hprefix tailTrace_365092
  have hstable : (prefixWord ++ tailWord_365092).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365092).length < 2 ^ (prefixWord ++ tailWord_365092).sum := by decide
  have hdescent : baseEnd_365092 < baseStart_365092 := by decide
  rcases family_descends (prefixWord ++ tailWord_365092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365154 : List Nat := [3, 3, 2, 3, 1, 1, 3, 1, 4]
def baseStart_365154 : Nat := 118140960795 + 365154 * 2 ^ 59
def prefixEnd_365154 : Nat := 4983230072969 + 3 ^ 40 * 365154 * 2
def baseEnd_365154 : Nat := 83333117738653140886975

theorem tailTrace_365154 : CollatzResearch.WordTrace tailWord_365154 prefixEnd_365154 83333117738653140886975 := by
  unfold tailWord_365154
  simp only [CollatzResearch.WordTrace]
  refine ⟨3329565129779224045827629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8878840346077930788873677 3329565129779224045827629)
  ·
    refine ⟨1248586923667209017185361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3329565129779224045827629 1248586923667209017185361)
    ·
      refine ⟨936440192750406762889021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1248586923667209017185361 936440192750406762889021)
      ·
        refine ⟨351165072281402536083383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 936440192750406762889021 351165072281402536083383)
        ·
          refine ⟨526747608422103804125075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351165072281402536083383 526747608422103804125075)
          ·
            refine ⟨790121412633155706187613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 526747608422103804125075 790121412633155706187613)
            ·
              refine ⟨296295529737433389820355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 790121412633155706187613 296295529737433389820355)
              ·
                refine ⟨444443294606150084730533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 296295529737433389820355 444443294606150084730533)
                ·
                  refine ⟨83333117738653140886975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 444443294606150084730533 83333117738653140886975)
                  ·
                    rfl

theorem cell21_365154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_365154 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_365154 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_365154 prefixEnd_365154 := by exact prefixLift 365154
  have htrace : WordTrace (prefixWord ++ tailWord_365154) baseStart_365154 baseEnd_365154 := by
    simpa [prefixWord, tailWord_365154, baseEnd_365154] using wordTrace_append hprefix tailTrace_365154
  have hstable : (prefixWord ++ tailWord_365154).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365154).length < 2 ^ (prefixWord ++ tailWord_365154).sum := by decide
  have hdescent : baseEnd_365154 < baseStart_365154 := by decide
  rcases family_descends (prefixWord ++ tailWord_365154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365176 : List Nat := [2, 1, 2, 1, 1, 1, 2, 11]
def baseStart_365176 : Nat := 118140960795 + 365176 * 2 ^ 59
def prefixEnd_365176 : Nat := 4983230072969 + 3 ^ 40 * 365176 * 2
def baseEnd_365176 : Nat := 27779379479461997173421

theorem tailTrace_365176 : CollatzResearch.WordTrace tailWord_365176 prefixEnd_365176 27779379479461997173421 := by
  unfold tailWord_365176
  simp only [CollatzResearch.WordTrace]
  refine ⟨6659531462518596970305691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8879375283358129293740921 6659531462518596970305691)
  ·
    refine ⟨9989297193777895455458537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6659531462518596970305691 9989297193777895455458537)
    ·
      refine ⟨7491972895333421591593903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9989297193777895455458537 7491972895333421591593903)
      ·
        refine ⟨11237959343000132387390855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7491972895333421591593903 11237959343000132387390855)
        ·
          refine ⟨16856939014500198581086283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11237959343000132387390855 16856939014500198581086283)
          ·
            refine ⟨25285408521750297871629425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16856939014500198581086283 25285408521750297871629425)
            ·
              refine ⟨18964056391312723403722069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25285408521750297871629425 18964056391312723403722069)
              ·
                refine ⟨27779379479461997173421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 18964056391312723403722069 27779379479461997173421)
                ·
                  rfl

theorem cell21_365176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 11].length) (baseStart_365176 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_365176 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_365176 prefixEnd_365176 := by exact prefixLift 365176
  have htrace : WordTrace (prefixWord ++ tailWord_365176) baseStart_365176 baseEnd_365176 := by
    simpa [prefixWord, tailWord_365176, baseEnd_365176] using wordTrace_append hprefix tailTrace_365176
  have hstable : (prefixWord ++ tailWord_365176).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365176).length < 2 ^ (prefixWord ++ tailWord_365176).sum := by decide
  have hdescent : baseEnd_365176 < baseStart_365176 := by decide
  rcases family_descends (prefixWord ++ tailWord_365176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365258 : List Nat := [3, 1, 2, 1, 4, 1, 4, 2, 3]
def baseStart_365258 : Nat := 118140960795 + 365258 * 2 ^ 59
def prefixEnd_365258 : Nat := 4983230072969 + 3 ^ 40 * 365258 * 2
def baseEnd_365258 : Nat := 83356851955572071153429

theorem tailTrace_365258 : CollatzResearch.WordTrace tailWord_365258 prefixEnd_365258 83356851955572071153429 := by
  unfold tailWord_365258
  simp only [CollatzResearch.WordTrace]
  refine ⟨3330513427685030486274107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8881369140493414630064285 3330513427685030486274107)
  ·
    refine ⟨4995770141527545729411161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3330513427685030486274107 4995770141527545729411161)
    ·
      refine ⟨3746827606145659297058371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4995770141527545729411161 3746827606145659297058371)
      ·
        refine ⟨5620241409218488945587557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3746827606145659297058371 5620241409218488945587557)
        ·
          refine ⟨1053795264228466677297667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5620241409218488945587557 1053795264228466677297667)
          ·
            refine ⟨1580692896342700015946501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1053795264228466677297667 1580692896342700015946501)
            ·
              refine ⟨296379918064256252989969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1580692896342700015946501 296379918064256252989969)
              ·
                refine ⟨222284938548192189742477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 296379918064256252989969 222284938548192189742477)
                ·
                  refine ⟨83356851955572071153429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 222284938548192189742477 83356851955572071153429)
                  ·
                    rfl

theorem cell21_365258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4, 2, 3].length) (baseStart_365258 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_365258 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_365258 prefixEnd_365258 := by exact prefixLift 365258
  have htrace : WordTrace (prefixWord ++ tailWord_365258) baseStart_365258 baseEnd_365258 := by
    simpa [prefixWord, tailWord_365258, baseEnd_365258] using wordTrace_append hprefix tailTrace_365258
  have hstable : (prefixWord ++ tailWord_365258).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365258).length < 2 ^ (prefixWord ++ tailWord_365258).sum := by decide
  have hdescent : baseEnd_365258 < baseStart_365258 := by decide
  rcases family_descends (prefixWord ++ tailWord_365258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365331 : List Nat := [1, 1, 1, 2, 1, 3, 7, 1, 4]
def baseStart_365331 : Nat := 118140960795 + 365331 * 2 ^ 59
def prefixEnd_365331 : Nat := 4983230072969 + 3 ^ 40 * 365331 * 2
def baseEnd_365331 : Nat := 83373511550140166436613

theorem tailTrace_365331 : CollatzResearch.WordTrace tailWord_365331 prefixEnd_365331 83373511550140166436613 := by
  unfold tailWord_365331
  simp only [CollatzResearch.WordTrace]
  refine ⟨13324716239475655412503847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8883144159650436941669231 13324716239475655412503847)
  ·
    refine ⟨19987074359213483118755771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13324716239475655412503847 19987074359213483118755771)
    ·
      refine ⟨29980611538820224678133657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19987074359213483118755771 29980611538820224678133657)
      ·
        refine ⟨22485458654115168508600243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29980611538820224678133657 22485458654115168508600243)
        ·
          refine ⟨33728187981172752762900365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22485458654115168508600243 33728187981172752762900365)
          ·
            refine ⟨12648070492939782286087637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33728187981172752762900365 12648070492939782286087637)
            ·
              refine ⟨296439152178276147330179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 12648070492939782286087637 296439152178276147330179)
              ·
                refine ⟨444658728267414220995269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 296439152178276147330179 444658728267414220995269)
                ·
                  refine ⟨83373511550140166436613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 444658728267414220995269 83373511550140166436613)
                  ·
                    rfl

theorem cell21_365331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7, 1, 4].length) (baseStart_365331 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_365331 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_365331 prefixEnd_365331 := by exact prefixLift 365331
  have htrace : WordTrace (prefixWord ++ tailWord_365331) baseStart_365331 baseEnd_365331 := by
    simpa [prefixWord, tailWord_365331, baseEnd_365331] using wordTrace_append hprefix tailTrace_365331
  have hstable : (prefixWord ++ tailWord_365331).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365331).length < 2 ^ (prefixWord ++ tailWord_365331).sum := by decide
  have hdescent : baseEnd_365331 < baseStart_365331 := by decide
  rcases family_descends (prefixWord ++ tailWord_365331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365376 : List Nat := [2, 1, 1, 2, 2, 1, 1, 8, 3]
def baseStart_365376 : Nat := 118140960795 + 365376 * 2 ^ 59
def prefixEnd_365376 : Nat := 4983230072969 + 3 ^ 40 * 365376 * 2
def baseEnd_365376 : Nat := 83383781163230088186521

theorem tailTrace_365376 : CollatzResearch.WordTrace tailWord_365376 prefixEnd_365376 83383781163230088186521 := by
  unfold tailWord_365376
  simp only [CollatzResearch.WordTrace]
  refine ⟨6663178762156314048945991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8884238349541752065261321 6663178762156314048945991)
  ·
    refine ⟨9994768143234471073418987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6663178762156314048945991 9994768143234471073418987)
    ·
      refine ⟨14992152214851706610128481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9994768143234471073418987 14992152214851706610128481)
      ·
        refine ⟨11244114161138779957596361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14992152214851706610128481 11244114161138779957596361)
        ·
          refine ⟨8433085620854084968197271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11244114161138779957596361 8433085620854084968197271)
          ·
            refine ⟨12649628431281127452295907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8433085620854084968197271 12649628431281127452295907)
            ·
              refine ⟨18974442646921691178443861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12649628431281127452295907 18974442646921691178443861)
              ·
                refine ⟨222356749768613568497389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 18974442646921691178443861 222356749768613568497389)
                ·
                  refine ⟨83383781163230088186521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 222356749768613568497389 83383781163230088186521)
                  ·
                    rfl

theorem cell21_365376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 8, 3].length) (baseStart_365376 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_365376 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_365376 prefixEnd_365376 := by exact prefixLift 365376
  have htrace : WordTrace (prefixWord ++ tailWord_365376) baseStart_365376 baseEnd_365376 := by
    simpa [prefixWord, tailWord_365376, baseEnd_365376] using wordTrace_append hprefix tailTrace_365376
  have hstable : (prefixWord ++ tailWord_365376).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365376).length < 2 ^ (prefixWord ++ tailWord_365376).sum := by decide
  have hdescent : baseEnd_365376 < baseStart_365376 := by decide
  rcases family_descends (prefixWord ++ tailWord_365376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365469 : List Nat := [1, 4, 2, 1, 2, 1, 4, 3, 3]
def baseStart_365469 : Nat := 118140960795 + 365469 * 2 ^ 59
def prefixEnd_365469 : Nat := 4983230072969 + 3 ^ 40 * 365469 * 2
def baseEnd_365469 : Nat := 83405005030282593136331

theorem tailTrace_365469 : CollatzResearch.WordTrace tailWord_365469 prefixEnd_365469 83405005030282593136331 := by
  unfold tailWord_365469
  simp only [CollatzResearch.WordTrace]
  refine ⟨13329749512975704981027461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8886499675317136654018307 13329749512975704981027461)
  ·
    refine ⟨2499328033682944683942649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13329749512975704981027461 2499328033682944683942649)
    ·
      refine ⟨1874496025262208512956987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2499328033682944683942649 1874496025262208512956987)
      ·
        refine ⟨2811744037893312769435481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1874496025262208512956987 2811744037893312769435481)
        ·
          refine ⟨2108808028419984577076611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2811744037893312769435481 2108808028419984577076611)
          ·
            refine ⟨3163212042629976865614917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2108808028419984577076611 3163212042629976865614917)
            ·
              refine ⟨593102257993120662302797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3163212042629976865614917 593102257993120662302797)
              ·
                refine ⟨222413346747420248363549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 593102257993120662302797 222413346747420248363549)
                ·
                  refine ⟨83405005030282593136331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 222413346747420248363549 83405005030282593136331)
                  ·
                    rfl

theorem cell21_365469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 3, 3].length) (baseStart_365469 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_365469 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_365469 prefixEnd_365469 := by exact prefixLift 365469
  have htrace : WordTrace (prefixWord ++ tailWord_365469) baseStart_365469 baseEnd_365469 := by
    simpa [prefixWord, tailWord_365469, baseEnd_365469] using wordTrace_append hprefix tailTrace_365469
  have hstable : (prefixWord ++ tailWord_365469).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365469).length < 2 ^ (prefixWord ++ tailWord_365469).sum := by decide
  have hdescent : baseEnd_365469 < baseStart_365469 := by decide
  rcases family_descends (prefixWord ++ tailWord_365469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365511 : List Nat := [1, 1, 4, 1, 1, 2, 4, 2, 5]
def baseStart_365511 : Nat := 118140960795 + 365511 * 2 ^ 59
def prefixEnd_365511 : Nat := 4983230072969 + 3 ^ 40 * 365511 * 2
def baseEnd_365511 : Nat := 83414590002499853436245

theorem tailTrace_365511 : CollatzResearch.WordTrace tailWord_365511 prefixEnd_365511 83414590002499853436245 := by
  unfold tailWord_365511
  simp only [CollatzResearch.WordTrace]
  refine ⟨13331281378823546154056387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8887520919215697436037591 13331281378823546154056387)
  ·
    refine ⟨19996922068235319231084581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13331281378823546154056387 19996922068235319231084581)
    ·
      refine ⟨3749422887794122355828359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19996922068235319231084581 3749422887794122355828359)
      ·
        refine ⟨5624134331691183533742539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3749422887794122355828359 5624134331691183533742539)
        ·
          refine ⟨8436201497536775300613809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5624134331691183533742539 8436201497536775300613809)
          ·
            refine ⟨6327151123152581475460357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8436201497536775300613809 6327151123152581475460357)
            ·
              refine ⟨1186340835591109026648817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6327151123152581475460357 1186340835591109026648817)
              ·
                refine ⟨889755626693331769986613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1186340835591109026648817 889755626693331769986613)
                ·
                  refine ⟨83414590002499853436245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 889755626693331769986613 83414590002499853436245)
                  ·
                    rfl

theorem cell21_365511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 2, 5].length) (baseStart_365511 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_365511 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_365511 prefixEnd_365511 := by exact prefixLift 365511
  have htrace : WordTrace (prefixWord ++ tailWord_365511) baseStart_365511 baseEnd_365511 := by
    simpa [prefixWord, tailWord_365511, baseEnd_365511] using wordTrace_append hprefix tailTrace_365511
  have hstable : (prefixWord ++ tailWord_365511).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365511).length < 2 ^ (prefixWord ++ tailWord_365511).sum := by decide
  have hdescent : baseEnd_365511 < baseStart_365511 := by decide
  rcases family_descends (prefixWord ++ tailWord_365511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365618 : List Nat := [3, 2, 1, 1, 2, 2, 1, 5, 4]
def baseStart_365618 : Nat := 118140960795 + 365618 * 2 ^ 59
def prefixEnd_365618 : Nat := 4983230072969 + 3 ^ 40 * 365618 * 2
def baseEnd_365618 : Nat := 83439008860291445152693

theorem tailTrace_365618 : CollatzResearch.WordTrace tailWord_365618 prefixEnd_365618 83439008860291445152693 := by
  unfold tailWord_365618
  simp only [CollatzResearch.WordTrace]
  refine ⟨3333795997358975857050377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8890122659623935618801005 3333795997358975857050377)
  ·
    refine ⟨2500346998019231892787783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3333795997358975857050377 2500346998019231892787783)
    ·
      refine ⟨3750520497028847839181675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2500346998019231892787783 3750520497028847839181675)
      ·
        refine ⟨5625780745543271758772513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3750520497028847839181675 5625780745543271758772513)
        ·
          refine ⟨4219335559157453819079385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5625780745543271758772513 4219335559157453819079385)
          ·
            refine ⟨3164501669368090364309539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4219335559157453819079385 3164501669368090364309539)
            ·
              refine ⟨4746752504052135546464309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3164501669368090364309539 4746752504052135546464309)
              ·
                refine ⟨445008047254887707481029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4746752504052135546464309 445008047254887707481029)
                ·
                  refine ⟨83439008860291445152693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 445008047254887707481029 83439008860291445152693)
                  ·
                    rfl

theorem cell21_365618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_365618 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_365618 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_365618 prefixEnd_365618 := by exact prefixLift 365618
  have htrace : WordTrace (prefixWord ++ tailWord_365618) baseStart_365618 baseEnd_365618 := by
    simpa [prefixWord, tailWord_365618, baseEnd_365618] using wordTrace_append hprefix tailTrace_365618
  have hstable : (prefixWord ++ tailWord_365618).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365618).length < 2 ^ (prefixWord ++ tailWord_365618).sum := by decide
  have hdescent : baseEnd_365618 < baseStart_365618 := by decide
  rcases family_descends (prefixWord ++ tailWord_365618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365638 : List Nat := [6, 1, 1, 1, 1, 2, 1, 5, 3]
def baseStart_365638 : Nat := 118140960795 + 365638 * 2 ^ 59
def prefixEnd_365638 : Nat := 4983230072969 + 3 ^ 40 * 365638 * 2
def baseEnd_365638 : Nat := 83443573132775854819319

theorem tailTrace_365638 : CollatzResearch.WordTrace tailWord_365638 prefixEnd_365638 83443573132775854819319 := by
  unfold tailWord_365638
  simp only [CollatzResearch.WordTrace]
  refine ⟨416747295292607713872799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8890608966242297895953045 416747295292607713872799)
  ·
    refine ⟨625120942938911570809199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 416747295292607713872799 625120942938911570809199)
    ·
      refine ⟨937681414408367356213799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 625120942938911570809199 937681414408367356213799)
      ·
        refine ⟨1406522121612551034320699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 937681414408367356213799 1406522121612551034320699)
        ·
          refine ⟨2109783182418826551481049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1406522121612551034320699 2109783182418826551481049)
          ·
            refine ⟨1582337386814119913610787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2109783182418826551481049 1582337386814119913610787)
            ·
              refine ⟨2373506080221179870416181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1582337386814119913610787 2373506080221179870416181)
              ·
                refine ⟨222516195020735612851517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2373506080221179870416181 222516195020735612851517)
                ·
                  refine ⟨83443573132775854819319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 222516195020735612851517 83443573132775854819319)
                  ·
                    rfl

theorem cell21_365638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_365638 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_365638 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_365638 prefixEnd_365638 := by exact prefixLift 365638
  have htrace : WordTrace (prefixWord ++ tailWord_365638) baseStart_365638 baseEnd_365638 := by
    simpa [prefixWord, tailWord_365638, baseEnd_365638] using wordTrace_append hprefix tailTrace_365638
  have hstable : (prefixWord ++ tailWord_365638).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365638).length < 2 ^ (prefixWord ++ tailWord_365638).sum := by decide
  have hdescent : baseEnd_365638 < baseStart_365638 := by decide
  rcases family_descends (prefixWord ++ tailWord_365638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365663 : List Nat := [1, 1, 2, 3, 1, 1, 6, 1, 5]
def baseStart_365663 : Nat := 118140960795 + 365663 * 2 ^ 59
def prefixEnd_365663 : Nat := 4983230072969 + 3 ^ 40 * 365663 * 2
def baseEnd_365663 : Nat := 83449278473381366902601

theorem tailTrace_365663 : CollatzResearch.WordTrace tailWord_365663 prefixEnd_365663 83449278473381366902601 := by
  unfold tailWord_365663
  simp only [CollatzResearch.WordTrace]
  refine ⟨13336825274272876113589643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8891216849515250742393095 13336825274272876113589643)
  ·
    refine ⟨20005237911409314170384465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13336825274272876113589643 20005237911409314170384465)
    ·
      refine ⟨15003928433556985627788349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20005237911409314170384465 15003928433556985627788349)
      ·
        refine ⟨5626473162583869610420631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15003928433556985627788349 5626473162583869610420631)
        ·
          refine ⟨8439709743875804415630947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5626473162583869610420631 8439709743875804415630947)
          ·
            refine ⟨12659564615813706623446421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8439709743875804415630947 12659564615813706623446421)
            ·
              refine ⟨593417091366267497974051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12659564615813706623446421 593417091366267497974051)
              ·
                refine ⟨890125637049401246961077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 593417091366267497974051 890125637049401246961077)
                ·
                  refine ⟨83449278473381366902601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 890125637049401246961077 83449278473381366902601)
                  ·
                    rfl

theorem cell21_365663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 1, 5].length) (baseStart_365663 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_365663 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_365663 prefixEnd_365663 := by exact prefixLift 365663
  have htrace : WordTrace (prefixWord ++ tailWord_365663) baseStart_365663 baseEnd_365663 := by
    simpa [prefixWord, tailWord_365663, baseEnd_365663] using wordTrace_append hprefix tailTrace_365663
  have hstable : (prefixWord ++ tailWord_365663).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365663).length < 2 ^ (prefixWord ++ tailWord_365663).sum := by decide
  have hdescent : baseEnd_365663 < baseStart_365663 := by decide
  rcases family_descends (prefixWord ++ tailWord_365663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365697 : List Nat := [1, 2, 4, 2, 2, 1, 3, 3, 3]
def baseStart_365697 : Nat := 118140960795 + 365697 * 2 ^ 59
def prefixEnd_365697 : Nat := 4983230072969 + 3 ^ 40 * 365697 * 2
def baseEnd_365697 : Nat := 83457037736604863335865

theorem tailTrace_365697 : CollatzResearch.WordTrace tailWord_365697 prefixEnd_365697 83457037736604863335865 := by
  unfold tailWord_365697
  simp only [CollatzResearch.WordTrace]
  refine ⟨13338065356149699920327345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8892043570766466613551563 13338065356149699920327345)
  ·
    refine ⟨10003549017112274940245509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13338065356149699920327345 10003549017112274940245509)
    ·
      refine ⟨1875665440708551551296033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10003549017112274940245509 1875665440708551551296033)
      ·
        refine ⟨1406749080531413663472025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1875665440708551551296033 1406749080531413663472025)
        ·
          refine ⟨1055061810398560247604019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1406749080531413663472025 1055061810398560247604019)
          ·
            refine ⟨1582592715597840371406029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1055061810398560247604019 1582592715597840371406029)
            ·
              refine ⟨593472268349190139277261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1582592715597840371406029 593472268349190139277261)
              ·
                refine ⟨222552100630946302228973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 593472268349190139277261 222552100630946302228973)
                ·
                  refine ⟨83457037736604863335865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 222552100630946302228973 83457037736604863335865)
                  ·
                    rfl

theorem cell21_365697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 3, 3].length) (baseStart_365697 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_365697 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_365697 prefixEnd_365697 := by exact prefixLift 365697
  have htrace : WordTrace (prefixWord ++ tailWord_365697) baseStart_365697 baseEnd_365697 := by
    simpa [prefixWord, tailWord_365697, baseEnd_365697] using wordTrace_append hprefix tailTrace_365697
  have hstable : (prefixWord ++ tailWord_365697).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365697).length < 2 ^ (prefixWord ++ tailWord_365697).sum := by decide
  have hdescent : baseEnd_365697 < baseStart_365697 := by decide
  rcases family_descends (prefixWord ++ tailWord_365697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365714 : List Nat := [3, 2, 3, 1, 1, 3, 3, 2, 3]
def baseStart_365714 : Nat := 118140960795 + 365714 * 2 ^ 59
def prefixEnd_365714 : Nat := 4983230072969 + 3 ^ 40 * 365714 * 2
def baseEnd_365714 : Nat := 83460917368216611552497

theorem tailTrace_365714 : CollatzResearch.WordTrace tailWord_365714 prefixEnd_365714 83460917368216611552497 := by
  unfold tailWord_365714
  simp only [CollatzResearch.WordTrace]
  refine ⟨3334671349272027955924049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8892456931392074549130797 3334671349272027955924049)
  ·
    refine ⟨2501003511954020966943037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3334671349272027955924049 2501003511954020966943037)
    ·
      refine ⟨937876316982757862603639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2501003511954020966943037 937876316982757862603639)
      ·
        refine ⟨1406814475474136793905459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 937876316982757862603639 1406814475474136793905459)
        ·
          refine ⟨2110221713211205190858189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1406814475474136793905459 2110221713211205190858189)
          ·
            refine ⟨791333142454201946571821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2110221713211205190858189 791333142454201946571821)
            ·
              refine ⟨296749928420325729964433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 791333142454201946571821 296749928420325729964433)
              ·
                refine ⟨222562446315244297473325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 296749928420325729964433 222562446315244297473325)
                ·
                  refine ⟨83460917368216611552497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 222562446315244297473325 83460917368216611552497)
                  ·
                    rfl

theorem cell21_365714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3, 2, 3].length) (baseStart_365714 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_365714 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_365714 prefixEnd_365714 := by exact prefixLift 365714
  have htrace : WordTrace (prefixWord ++ tailWord_365714) baseStart_365714 baseEnd_365714 := by
    simpa [prefixWord, tailWord_365714, baseEnd_365714] using wordTrace_append hprefix tailTrace_365714
  have hstable : (prefixWord ++ tailWord_365714).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365714).length < 2 ^ (prefixWord ++ tailWord_365714).sum := by decide
  have hdescent : baseEnd_365714 < baseStart_365714 := by decide
  rcases family_descends (prefixWord ++ tailWord_365714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365770 : List Nat := [3, 1, 2, 1, 3, 2, 1, 4, 4]
def baseStart_365770 : Nat := 118140960795 + 365770 * 2 ^ 59
def prefixEnd_365770 : Nat := 4983230072969 + 3 ^ 40 * 365770 * 2
def baseEnd_365770 : Nat := 83473697331172958619049

theorem tailTrace_365770 : CollatzResearch.WordTrace tailWord_365770 prefixEnd_365770 83473697331172958619049 := by
  unfold tailWord_365770
  simp only [CollatzResearch.WordTrace]
  refine ⟨3335181971221308346933691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8893818589923488925156509 3335181971221308346933691)
  ·
    refine ⟨5002772956831962520400537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3335181971221308346933691 5002772956831962520400537)
    ·
      refine ⟨3752079717623971890300403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5002772956831962520400537 3752079717623971890300403)
      ·
        refine ⟨5628119576435957835450605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3752079717623971890300403 5628119576435957835450605)
        ·
          refine ⟨2110544841163484188293977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5628119576435957835450605 2110544841163484188293977)
          ·
            refine ⟨1582908630872613141220483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2110544841163484188293977 1582908630872613141220483)
            ·
              refine ⟨2374362946308919711830725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1582908630872613141220483 2374362946308919711830725)
              ·
                refine ⟨445193052432922445968261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2374362946308919711830725 445193052432922445968261)
                ·
                  refine ⟨83473697331172958619049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 445193052432922445968261 83473697331172958619049)
                  ·
                    rfl

theorem cell21_365770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 4, 4].length) (baseStart_365770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_365770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_365770 prefixEnd_365770 := by exact prefixLift 365770
  have htrace : WordTrace (prefixWord ++ tailWord_365770) baseStart_365770 baseEnd_365770 := by
    simpa [prefixWord, tailWord_365770, baseEnd_365770] using wordTrace_append hprefix tailTrace_365770
  have hstable : (prefixWord ++ tailWord_365770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365770).length < 2 ^ (prefixWord ++ tailWord_365770).sum := by decide
  have hdescent : baseEnd_365770 < baseStart_365770 := by decide
  rcases family_descends (prefixWord ++ tailWord_365770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365829 : List Nat := [1, 3, 1, 1, 2, 1, 5, 1, 6]
def baseStart_365829 : Nat := 118140960795 + 365829 * 2 ^ 59
def prefixEnd_365829 : Nat := 4983230072969 + 3 ^ 40 * 365829 * 2
def baseEnd_365829 : Nat := 83487161935001967135595

theorem tailTrace_365829 : CollatzResearch.WordTrace tailWord_365829 prefixEnd_365829 83487161935001967135595 := by
  unfold tailWord_365829
  simp only [CollatzResearch.WordTrace]
  refine ⟨13342879791671486464132541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8895253194447657642755027 13342879791671486464132541)
  ·
    refine ⟨5003579921876807424049703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13342879791671486464132541 5003579921876807424049703)
    ·
      refine ⟨7505369882815211136074555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5003579921876807424049703 7505369882815211136074555)
      ·
        refine ⟨11258054824222816704111833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7505369882815211136074555 11258054824222816704111833)
        ·
          refine ⟨8443541118167112528083875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11258054824222816704111833 8443541118167112528083875)
          ·
            refine ⟨12665311677250668792125813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8443541118167112528083875 12665311677250668792125813)
            ·
              refine ⟨1187372969742250199261795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12665311677250668792125813 1187372969742250199261795)
              ·
                refine ⟨1781059454613375298892693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1187372969742250199261795 1781059454613375298892693)
                ·
                  refine ⟨83487161935001967135595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1781059454613375298892693 83487161935001967135595)
                  ·
                    rfl

theorem cell21_365829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 6].length) (baseStart_365829 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_365829 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_365829 prefixEnd_365829 := by exact prefixLift 365829
  have htrace : WordTrace (prefixWord ++ tailWord_365829) baseStart_365829 baseEnd_365829 := by
    simpa [prefixWord, tailWord_365829, baseEnd_365829] using wordTrace_append hprefix tailTrace_365829
  have hstable : (prefixWord ++ tailWord_365829).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365829).length < 2 ^ (prefixWord ++ tailWord_365829).sum := by decide
  have hdescent : baseEnd_365829 < baseStart_365829 := by decide
  rcases family_descends (prefixWord ++ tailWord_365829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365832 : List Nat := [2, 1, 3, 2, 4, 1, 2, 1, 5]
def baseStart_365832 : Nat := 118140960795 + 365832 * 2 ^ 59
def prefixEnd_365832 : Nat := 4983230072969 + 3 ^ 40 * 365832 * 2
def baseEnd_365832 : Nat := 83487846575874628585589

theorem tailTrace_365832 : CollatzResearch.WordTrace tailWord_365832 prefixEnd_365832 83487846575874628585589 := by
  unfold tailWord_365832
  simp only [CollatzResearch.WordTrace]
  refine ⟨6671494605330308988245875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8895326140440411984327833 6671494605330308988245875)
  ·
    refine ⟨10007241907995463482368813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6671494605330308988245875 10007241907995463482368813)
    ·
      refine ⟨3752715715498298805888305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10007241907995463482368813 3752715715498298805888305)
      ·
        refine ⟨2814536786623724104416229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3752715715498298805888305 2814536786623724104416229)
        ·
          refine ⟨527725647491948269578043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2814536786623724104416229 527725647491948269578043)
          ·
            refine ⟨791588471237922404367065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 527725647491948269578043 791588471237922404367065)
            ·
              refine ⟨593691353428441803275299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 791588471237922404367065 593691353428441803275299)
              ·
                refine ⟨890537030142662704912949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 593691353428441803275299 890537030142662704912949)
                ·
                  refine ⟨83487846575874628585589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 890537030142662704912949 83487846575874628585589)
                  ·
                    rfl

theorem cell21_365832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 1, 5].length) (baseStart_365832 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_365832 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_365832 prefixEnd_365832 := by exact prefixLift 365832
  have htrace : WordTrace (prefixWord ++ tailWord_365832) baseStart_365832 baseEnd_365832 := by
    simpa [prefixWord, tailWord_365832, baseEnd_365832] using wordTrace_append hprefix tailTrace_365832
  have hstable : (prefixWord ++ tailWord_365832).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365832).length < 2 ^ (prefixWord ++ tailWord_365832).sum := by decide
  have hdescent : baseEnd_365832 < baseStart_365832 := by decide
  rcases family_descends (prefixWord ++ tailWord_365832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365860 : List Nat := [2, 3, 1, 3, 1, 1, 3, 7]
def baseStart_365860 : Nat := 118140960795 + 365860 * 2 ^ 59
def prefixEnd_365860 : Nat := 4983230072969 + 3 ^ 40 * 365860 * 2
def baseEnd_365860 : Nat := 27831412185784267372955

theorem tailTrace_365860 : CollatzResearch.WordTrace tailWord_365860 prefixEnd_365860 27831412185784267372955 := by
  unfold tailWord_365860
  simp only [CollatzResearch.WordTrace]
  refine ⟨6672005227279589379255517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8896006969706119172340689 6672005227279589379255517)
  ·
    refine ⟨2502001960229846017220819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6672005227279589379255517 2502001960229846017220819)
    ·
      refine ⟨3753002940344769025831229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2502001960229846017220819 3753002940344769025831229)
      ·
        refine ⟨1407376102629288384686711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3753002940344769025831229 1407376102629288384686711)
        ·
          refine ⟨2111064153943932577030067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1407376102629288384686711 2111064153943932577030067)
          ·
            refine ⟨3166596230915898865545101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2111064153943932577030067 3166596230915898865545101)
            ·
              refine ⟨1187473586593462074579413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3166596230915898865545101 1187473586593462074579413)
              ·
                refine ⟨27831412185784267372955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1187473586593462074579413 27831412185784267372955)
                ·
                  rfl

theorem cell21_365860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 7].length) (baseStart_365860 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_365860 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_365860 prefixEnd_365860 := by exact prefixLift 365860
  have htrace : WordTrace (prefixWord ++ tailWord_365860) baseStart_365860 baseEnd_365860 := by
    simpa [prefixWord, tailWord_365860, baseEnd_365860] using wordTrace_append hprefix tailTrace_365860
  have hstable : (prefixWord ++ tailWord_365860).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365860).length < 2 ^ (prefixWord ++ tailWord_365860).sum := by decide
  have hdescent : baseEnd_365860 < baseStart_365860 := by decide
  rcases family_descends (prefixWord ++ tailWord_365860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365866 : List Nat := [3, 1, 4, 2, 1, 3, 1, 3, 3]
def baseStart_365866 : Nat := 118140960795 + 365866 * 2 ^ 59
def prefixEnd_365866 : Nat := 4983230072969 + 3 ^ 40 * 365866 * 2
def baseEnd_365866 : Nat := 83495605839098125018853

theorem tailTrace_365866 : CollatzResearch.WordTrace tailWord_365866 prefixEnd_365866 83495605839098125018853 := by
  unfold tailWord_365866
  simp only [CollatzResearch.WordTrace]
  refine ⟨3336057323134360445807363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8896152861691627855486301 3336057323134360445807363)
  ·
    refine ⟨5004085984701540668711045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3336057323134360445807363 5004085984701540668711045)
    ·
      refine ⟨938266122131538875383321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5004085984701540668711045 938266122131538875383321)
      ·
        refine ⟨703699591598654156537491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 938266122131538875383321 703699591598654156537491)
        ·
          refine ⟨1055549387397981234806237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 703699591598654156537491 1055549387397981234806237)
          ·
            refine ⟨395831020274242963052339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1055549387397981234806237 395831020274242963052339)
            ·
              refine ⟨593746530411364444578509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 395831020274242963052339 593746530411364444578509)
              ·
                refine ⟨222654948904261666716941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 593746530411364444578509 222654948904261666716941)
                ·
                  refine ⟨83495605839098125018853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 222654948904261666716941 83495605839098125018853)
                  ·
                    rfl

theorem cell21_365866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 3, 3].length) (baseStart_365866 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_365866 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_365866 prefixEnd_365866 := by exact prefixLift 365866
  have htrace : WordTrace (prefixWord ++ tailWord_365866) baseStart_365866 baseEnd_365866 := by
    simpa [prefixWord, tailWord_365866, baseEnd_365866] using wordTrace_append hprefix tailTrace_365866
  have hstable : (prefixWord ++ tailWord_365866).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365866).length < 2 ^ (prefixWord ++ tailWord_365866).sum := by decide
  have hdescent : baseEnd_365866 < baseStart_365866 := by decide
  rcases family_descends (prefixWord ++ tailWord_365866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365984 : List Nat := [2, 1, 1, 4, 1, 2, 4, 3, 3]
def baseStart_365984 : Nat := 118140960795 + 365984 * 2 ^ 59
def prefixEnd_365984 : Nat := 4983230072969 + 3 ^ 40 * 365984 * 2
def baseEnd_365984 : Nat := 83522535046756142051945

theorem tailTrace_365984 : CollatzResearch.WordTrace tailWord_365984 prefixEnd_365984 83522535046756142051945 := by
  unfold tailWord_365984
  simp only [CollatzResearch.WordTrace]
  refine ⟨6674266553054973968012503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8899022070739965290683337 6674266553054973968012503)
  ·
    refine ⟨10011399829582460952018755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6674266553054973968012503 10011399829582460952018755)
    ·
      refine ⟨15017099744373691428028133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10011399829582460952018755 15017099744373691428028133)
      ·
        refine ⟨2815706202070067142755275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15017099744373691428028133 2815706202070067142755275)
        ·
          refine ⟨4223559303105100714132913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2815706202070067142755275 4223559303105100714132913)
          ·
            refine ⟨3167669477328825535599685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4223559303105100714132913 3167669477328825535599685)
            ·
              refine ⟨593938026999154787924941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3167669477328825535599685 593938026999154787924941)
              ·
                refine ⟨222726760124683045471853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 593938026999154787924941 222726760124683045471853)
                ·
                  refine ⟨83522535046756142051945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 222726760124683045471853 83522535046756142051945)
                  ·
                    rfl

theorem cell21_365984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 3, 3].length) (baseStart_365984 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_365984 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_365984 prefixEnd_365984 := by exact prefixLift 365984
  have htrace : WordTrace (prefixWord ++ tailWord_365984) baseStart_365984 baseEnd_365984 := by
    simpa [prefixWord, tailWord_365984, baseEnd_365984] using wordTrace_append hprefix tailTrace_365984
  have hstable : (prefixWord ++ tailWord_365984).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365984).length < 2 ^ (prefixWord ++ tailWord_365984).sum := by decide
  have hdescent : baseEnd_365984 < baseStart_365984 := by decide
  rcases family_descends (prefixWord ++ tailWord_365984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366198 : List Nat := [5, 1, 1, 2, 2, 3, 2, 5]
def baseStart_366198 : Nat := 118140960795 + 366198 * 2 ^ 59
def prefixEnd_366198 : Nat := 4983230072969 + 3 ^ 40 * 366198 * 2
def baseEnd_366198 : Nat := 27857124254113108494947

theorem tailTrace_366198 : CollatzResearch.WordTrace tailWord_366198 prefixEnd_366198 27857124254113108494947 := by
  unfold tailWord_366198
  simp only [CollatzResearch.WordTrace]
  refine ⟨834771145458416405269703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8904225551556441656210165 834771145458416405269703)
  ·
    refine ⟨1252156718187624607904555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 834771145458416405269703 1252156718187624607904555)
    ·
      refine ⟨1878235077281436911856833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1252156718187624607904555 1878235077281436911856833)
      ·
        refine ⟨1408676307961077683892625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1878235077281436911856833 1408676307961077683892625)
        ·
          refine ⟨1056507230970808262919469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1408676307961077683892625 1056507230970808262919469)
          ·
            refine ⟨396190211614053098594801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1056507230970808262919469 396190211614053098594801)
            ·
              refine ⟨297142658710539823946101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 396190211614053098594801 297142658710539823946101)
              ·
                refine ⟨27857124254113108494947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 297142658710539823946101 27857124254113108494947)
                ·
                  rfl

theorem cell21_366198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_366198 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_366198 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_366198 prefixEnd_366198 := by exact prefixLift 366198
  have htrace : WordTrace (prefixWord ++ tailWord_366198) baseStart_366198 baseEnd_366198 := by
    simpa [prefixWord, tailWord_366198, baseEnd_366198] using wordTrace_append hprefix tailTrace_366198
  have hstable : (prefixWord ++ tailWord_366198).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366198).length < 2 ^ (prefixWord ++ tailWord_366198).sum := by decide
  have hdescent : baseEnd_366198 < baseStart_366198 := by decide
  rcases family_descends (prefixWord ++ tailWord_366198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366209 : List Nat := [1, 2, 4, 2, 1, 2, 1, 2, 6]
def baseStart_366209 : Nat := 118140960795 + 366209 * 2 ^ 59
def prefixEnd_366209 : Nat := 4983230072969 + 3 ^ 40 * 366209 * 2
def baseEnd_366209 : Nat := 83573883112205750801485

theorem tailTrace_366209 : CollatzResearch.WordTrace tailWord_366209 prefixEnd_366209 83573883112205750801485 := by
  unfold tailWord_366209
  simp only [CollatzResearch.WordTrace]
  refine ⟨13356739530294811362965681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8904493020196540908643787 13356739530294811362965681)
  ·
    refine ⟨10017554647721108522224261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13356739530294811362965681 10017554647721108522224261)
    ·
      refine ⟨1878291496447707847917049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10017554647721108522224261 1878291496447707847917049)
      ·
        refine ⟨1408718622335780885937787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1878291496447707847917049 1408718622335780885937787)
        ·
          refine ⟨2113077933503671328906681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1408718622335780885937787 2113077933503671328906681)
          ·
            refine ⟨1584808450127753496680011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2113077933503671328906681 1584808450127753496680011)
            ·
              refine ⟨2377212675191630245020017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1584808450127753496680011 2377212675191630245020017)
              ·
                refine ⟨1782909506393722683765013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2377212675191630245020017 1782909506393722683765013)
                ·
                  refine ⟨83573883112205750801485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1782909506393722683765013 83573883112205750801485)
                  ·
                    rfl

theorem cell21_366209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 6].length) (baseStart_366209 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_366209 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_366209 prefixEnd_366209 := by exact prefixLift 366209
  have htrace : WordTrace (prefixWord ++ tailWord_366209) baseStart_366209 baseEnd_366209 := by
    simpa [prefixWord, tailWord_366209, baseEnd_366209] using wordTrace_append hprefix tailTrace_366209
  have hstable : (prefixWord ++ tailWord_366209).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366209).length < 2 ^ (prefixWord ++ tailWord_366209).sum := by decide
  have hdescent : baseEnd_366209 < baseStart_366209 := by decide
  rcases family_descends (prefixWord ++ tailWord_366209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366240 : List Nat := [2, 1, 1, 4, 3, 2, 2, 6]
def baseStart_366240 : Nat := 118140960795 + 366240 * 2 ^ 59
def prefixEnd_366240 : Nat := 4983230072969 + 3 ^ 40 * 366240 * 2
def baseEnd_366240 : Nat := 27860319244852195261585

theorem tailTrace_366240 : CollatzResearch.WordTrace tailWord_366240 prefixEnd_366240 27860319244852195261585 := by
  unfold tailWord_366240
  simp only [CollatzResearch.WordTrace]
  refine ⟨6678935096591251828672087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8905246795455002438229449 6678935096591251828672087)
  ·
    refine ⟨10018402644886877743008131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6678935096591251828672087 10018402644886877743008131)
    ·
      refine ⟨15027603967330316614512197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10018402644886877743008131 15027603967330316614512197)
      ·
        refine ⟨2817675743874434365221037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15027603967330316614512197 2817675743874434365221037)
        ·
          refine ⟨1056628403952912886957889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2817675743874434365221037 1056628403952912886957889)
          ·
            refine ⟨792471302964684665218417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1056628403952912886957889 792471302964684665218417)
            ·
              refine ⟨594353477223513498913813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 792471302964684665218417 594353477223513498913813)
              ·
                refine ⟨27860319244852195261585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 594353477223513498913813 27860319244852195261585)
                ·
                  rfl

theorem cell21_366240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 6].length) (baseStart_366240 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_366240 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_366240 prefixEnd_366240 := by exact prefixLift 366240
  have htrace : WordTrace (prefixWord ++ tailWord_366240) baseStart_366240 baseEnd_366240 := by
    simpa [prefixWord, tailWord_366240, baseEnd_366240] using wordTrace_append hprefix tailTrace_366240
  have hstable : (prefixWord ++ tailWord_366240).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366240).length < 2 ^ (prefixWord ++ tailWord_366240).sum := by decide
  have hdescent : baseEnd_366240 < baseStart_366240 := by decide
  rcases family_descends (prefixWord ++ tailWord_366240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366271 : List Nat := [1, 1, 2, 2, 2, 3, 2, 5, 3]
def baseStart_366271 : Nat := 118140960795 + 366271 * 2 ^ 59
def prefixEnd_366271 : Nat := 4983230072969 + 3 ^ 40 * 366271 * 2
def baseEnd_366271 : Nat := 83588032356907420768025

theorem tailTrace_366271 : CollatzResearch.WordTrace tailWord_366271 prefixEnd_366271 83588032356907420768025 := by
  unfold tailWord_366271
  simp only [CollatzResearch.WordTrace]
  refine ⟨13359000856070195951722667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8906000570713463967815111 13359000856070195951722667)
  ·
    refine ⟨20038501284105293927584001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13359000856070195951722667 20038501284105293927584001)
    ·
      refine ⟨15028875963078970445688001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20038501284105293927584001 15028875963078970445688001)
      ·
        refine ⟨11271656972309227834266001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15028875963078970445688001 11271656972309227834266001)
        ·
          refine ⟨8453742729231920875699501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11271656972309227834266001 8453742729231920875699501)
          ·
            refine ⟨3170153523461970328387313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8453742729231920875699501 3170153523461970328387313)
            ·
              refine ⟨2377615142596477746290485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3170153523461970328387313 2377615142596477746290485)
              ·
                refine ⟨222901419618419788714733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2377615142596477746290485 222901419618419788714733)
                ·
                  refine ⟨83588032356907420768025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 222901419618419788714733 83588032356907420768025)
                  ·
                    rfl

theorem cell21_366271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 5, 3].length) (baseStart_366271 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_366271 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_366271 prefixEnd_366271 := by exact prefixLift 366271
  have htrace : WordTrace (prefixWord ++ tailWord_366271) baseStart_366271 baseEnd_366271 := by
    simpa [prefixWord, tailWord_366271, baseEnd_366271] using wordTrace_append hprefix tailTrace_366271
  have hstable : (prefixWord ++ tailWord_366271).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366271).length < 2 ^ (prefixWord ++ tailWord_366271).sum := by decide
  have hdescent : baseEnd_366271 < baseStart_366271 := by decide
  rcases family_descends (prefixWord ++ tailWord_366271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366274 : List Nat := [3, 5, 1, 2, 1, 9]
def baseStart_366274 : Nat := 118140960795 + 366274 * 2 ^ 59
def prefixEnd_366274 : Nat := 4983230072969 + 3 ^ 40 * 366274 * 2
def baseEnd_366274 : Nat := 3095878407325188230297

theorem tailTrace_366274 : CollatzResearch.WordTrace tailWord_366274 prefixEnd_366274 3095878407325188230297 := by
  unfold tailWord_366274
  simp only [CollatzResearch.WordTrace]
  refine ⟨3339777568764831866020469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8906073516706218309387917 3339777568764831866020469)
  ·
    refine ⟨313104147071702987439419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3339777568764831866020469 313104147071702987439419)
    ·
      refine ⟨469656220607554481159129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313104147071702987439419 469656220607554481159129)
      ·
        refine ⟨352242165455665860869347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 469656220607554481159129 352242165455665860869347)
        ·
          refine ⟨528363248183498791304021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352242165455665860869347 528363248183498791304021)
          ·
            refine ⟨3095878407325188230297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 528363248183498791304021 3095878407325188230297)
            ·
              rfl

theorem cell21_366274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 9].length) (baseStart_366274 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_366274 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_366274 prefixEnd_366274 := by exact prefixLift 366274
  have htrace : WordTrace (prefixWord ++ tailWord_366274) baseStart_366274 baseEnd_366274 := by
    simpa [prefixWord, tailWord_366274, baseEnd_366274] using wordTrace_append hprefix tailTrace_366274
  have hstable : (prefixWord ++ tailWord_366274).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366274).length < 2 ^ (prefixWord ++ tailWord_366274).sum := by decide
  have hdescent : baseEnd_366274 < baseStart_366274 := by decide
  rcases family_descends (prefixWord ++ tailWord_366274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366347 : List Nat := [1, 1, 1, 1, 5, 1, 4, 4, 3]
def baseStart_366347 : Nat := 118140960795 + 366347 * 2 ^ 59
def prefixEnd_366347 : Nat := 4983230072969 + 3 ^ 40 * 366347 * 2
def baseEnd_366347 : Nat := 83605376592348177501203

theorem tailTrace_366347 : CollatzResearch.WordTrace tailWord_366347 prefixEnd_366347 83605376592348177501203 := by
  unfold tailWord_366347
  simp only [CollatzResearch.WordTrace]
  refine ⟨13361772803794860931489295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8907848535863240620992863 13361772803794860931489295)
  ·
    refine ⟨20042659205692291397233943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13361772803794860931489295 20042659205692291397233943)
    ·
      refine ⟨30063988808538437095850915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20042659205692291397233943 30063988808538437095850915)
      ·
        refine ⟨45095983212807655643776373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30063988808538437095850915 45095983212807655643776373)
        ·
          refine ⟨4227748426200717716604035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45095983212807655643776373 4227748426200717716604035)
          ·
            refine ⟨6341622639301076574906053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4227748426200717716604035 6341622639301076574906053)
            ·
              refine ⟨1189054244868951857794885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6341622639301076574906053 1189054244868951857794885)
              ·
                refine ⟨222947670912928473336541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1189054244868951857794885 222947670912928473336541)
                ·
                  refine ⟨83605376592348177501203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 222947670912928473336541 83605376592348177501203)
                  ·
                    rfl

theorem cell21_366347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 4, 3].length) (baseStart_366347 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_366347 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_366347 prefixEnd_366347 := by exact prefixLift 366347
  have htrace : WordTrace (prefixWord ++ tailWord_366347) baseStart_366347 baseEnd_366347 := by
    simpa [prefixWord, tailWord_366347, baseEnd_366347] using wordTrace_append hprefix tailTrace_366347
  have hstable : (prefixWord ++ tailWord_366347).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366347).length < 2 ^ (prefixWord ++ tailWord_366347).sum := by decide
  have hdescent : baseEnd_366347 < baseStart_366347 := by decide
  rcases family_descends (prefixWord ++ tailWord_366347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366412 : List Nat := [2, 2, 1, 3, 5, 1, 2, 1, 4]
def baseStart_366412 : Nat := 118140960795 + 366412 * 2 ^ 59
def prefixEnd_366412 : Nat := 4983230072969 + 3 ^ 40 * 366412 * 2
def baseEnd_366412 : Nat := 83620210477922508917737

theorem tailTrace_366412 : CollatzResearch.WordTrace tailWord_366412 prefixEnd_366412 83620210477922508917737 := by
  unfold tailWord_366412
  simp only [CollatzResearch.WordTrace]
  refine ⟨6682071774279688516302745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8909429032372918021736993 6682071774279688516302745)
  ·
    refine ⟨5011553830709766387227059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6682071774279688516302745 5011553830709766387227059)
    ·
      refine ⟨7517330746064649580840589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5011553830709766387227059 7517330746064649580840589)
      ·
        refine ⟨2818999029774243592815221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7517330746064649580840589 2818999029774243592815221)
        ·
          refine ⟨264281159041335336826427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2818999029774243592815221 264281159041335336826427)
          ·
            refine ⟨396421738562003005239641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264281159041335336826427 396421738562003005239641)
            ·
              refine ⟨297316303921502253929731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 396421738562003005239641 297316303921502253929731)
              ·
                refine ⟨445974455882253380894597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 297316303921502253929731 445974455882253380894597)
                ·
                  refine ⟨83620210477922508917737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 445974455882253380894597 83620210477922508917737)
                  ·
                    rfl

theorem cell21_366412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 2, 1, 4].length) (baseStart_366412 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_366412 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_366412 prefixEnd_366412 := by exact prefixLift 366412
  have htrace : WordTrace (prefixWord ++ tailWord_366412) baseStart_366412 baseEnd_366412 := by
    simpa [prefixWord, tailWord_366412, baseEnd_366412] using wordTrace_append hprefix tailTrace_366412
  have hstable : (prefixWord ++ tailWord_366412).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366412).length < 2 ^ (prefixWord ++ tailWord_366412).sum := by decide
  have hdescent : baseEnd_366412 < baseStart_366412 := by decide
  rcases family_descends (prefixWord ++ tailWord_366412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366496 : List Nat := [2, 1, 1, 4, 1, 1, 1, 4, 6]
def baseStart_366496 : Nat := 118140960795 + 366496 * 2 ^ 59
def prefixEnd_366496 : Nat := 4983230072969 + 3 ^ 40 * 366496 * 2
def baseEnd_366496 : Nat := 83639380422357029517565

theorem tailTrace_366496 : CollatzResearch.WordTrace tailWord_366496 prefixEnd_366496 83639380422357029517565 := by
  unfold tailWord_366496
  simp only [CollatzResearch.WordTrace]
  refine ⟨6683603640127529689331671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8911471520170039585775561 6683603640127529689331671)
  ·
    refine ⟨10025405460191294533997507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6683603640127529689331671 10025405460191294533997507)
    ·
      refine ⟨15038108190286941800996261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10025405460191294533997507 15038108190286941800996261)
      ·
        refine ⟨2819645285678801587686799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15038108190286941800996261 2819645285678801587686799)
        ·
          refine ⟨4229467928518202381530199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2819645285678801587686799 4229467928518202381530199)
          ·
            refine ⟨6344201892777303572295299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4229467928518202381530199 6344201892777303572295299)
            ·
              refine ⟨9516302839165955358442949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6344201892777303572295299 9516302839165955358442949)
              ·
                refine ⟨1784306782343616629708053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9516302839165955358442949 1784306782343616629708053)
                ·
                  refine ⟨83639380422357029517565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1784306782343616629708053 83639380422357029517565)
                  ·
                    rfl

theorem cell21_366496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 6].length) (baseStart_366496 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_366496 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_366496 prefixEnd_366496 := by exact prefixLift 366496
  have htrace : WordTrace (prefixWord ++ tailWord_366496) baseStart_366496 baseEnd_366496 := by
    simpa [prefixWord, tailWord_366496, baseEnd_366496] using wordTrace_append hprefix tailTrace_366496
  have hstable : (prefixWord ++ tailWord_366496).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366496).length < 2 ^ (prefixWord ++ tailWord_366496).sum := by decide
  have hdescent : baseEnd_366496 < baseStart_366496 := by decide
  rcases family_descends (prefixWord ++ tailWord_366496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366513 : List Nat := [1, 2, 2, 4, 2, 2, 1, 1, 6]
def baseStart_366513 : Nat := 118140960795 + 366513 * 2 ^ 59
def prefixEnd_366513 : Nat := 4983230072969 + 3 ^ 40 * 366513 * 2
def baseEnd_366513 : Nat := 83643260053968777734197

theorem tailTrace_366513 : CollatzResearch.WordTrace tailWord_366513 prefixEnd_366513 83643260053968777734197 := by
  unfold tailWord_366513
  simp only [CollatzResearch.WordTrace]
  refine ⟨13367827321193471282032193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8911884880795647521354795 13367827321193471282032193)
  ·
    refine ⟨10025870490895103461524145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13367827321193471282032193 10025870490895103461524145)
    ·
      refine ⟨7519402868171327596143109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10025870490895103461524145 7519402868171327596143109)
      ·
        refine ⟨1409888037782123924276833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7519402868171327596143109 1409888037782123924276833)
        ·
          refine ⟨1057416028336592943207625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1409888037782123924276833 1057416028336592943207625)
          ·
            refine ⟨793062021252444707405719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1057416028336592943207625 793062021252444707405719)
            ·
              refine ⟨1189593031878667061108579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 793062021252444707405719 1189593031878667061108579)
              ·
                refine ⟨1784389547818000591662869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1189593031878667061108579 1784389547818000591662869)
                ·
                  refine ⟨83643260053968777734197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1784389547818000591662869 83643260053968777734197)
                  ·
                    rfl

theorem cell21_366513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 6].length) (baseStart_366513 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_366513 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_366513 prefixEnd_366513 := by exact prefixLift 366513
  have htrace : WordTrace (prefixWord ++ tailWord_366513) baseStart_366513 baseEnd_366513 := by
    simpa [prefixWord, tailWord_366513, baseEnd_366513] using wordTrace_append hprefix tailTrace_366513
  have hstable : (prefixWord ++ tailWord_366513).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366513).length < 2 ^ (prefixWord ++ tailWord_366513).sum := by decide
  have hdescent : baseEnd_366513 < baseStart_366513 := by decide
  rcases family_descends (prefixWord ++ tailWord_366513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366550 : List Nat := [5, 2, 1, 1, 3, 2, 1, 3, 3]
def baseStart_366550 : Nat := 118140960795 + 366550 * 2 ^ 59
def prefixEnd_366550 : Nat := 4983230072969 + 3 ^ 40 * 366550 * 2
def baseEnd_366550 : Nat := 83651703958064935617455

theorem tailTrace_366550 : CollatzResearch.WordTrace tailWord_366550 prefixEnd_366550 83651703958064935617455 := by
  unfold tailWord_366550
  simp only [CollatzResearch.WordTrace]
  refine ⟨835573551378714162570569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8912784548039617734086069 835573551378714162570569)
  ·
    refine ⟨626680163534035621927927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 835573551378714162570569 626680163534035621927927)
    ·
      refine ⟨940020245301053432891891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 626680163534035621927927 940020245301053432891891)
      ·
        refine ⟨1410030367951580149337837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 940020245301053432891891 1410030367951580149337837)
        ·
          refine ⟨528761387981842556001689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1410030367951580149337837 528761387981842556001689)
          ·
            refine ⟨396571040986381917001267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 528761387981842556001689 396571040986381917001267)
            ·
              refine ⟨594856561479572875501901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 396571040986381917001267 594856561479572875501901)
              ·
                refine ⟨223071210554839828313213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 594856561479572875501901 223071210554839828313213)
                ·
                  refine ⟨83651703958064935617455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 223071210554839828313213 83651703958064935617455)
                  ·
                    rfl

theorem cell21_366550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_366550 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_366550 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_366550 prefixEnd_366550 := by exact prefixLift 366550
  have htrace : WordTrace (prefixWord ++ tailWord_366550) baseStart_366550 baseEnd_366550 := by
    simpa [prefixWord, tailWord_366550, baseEnd_366550] using wordTrace_append hprefix tailTrace_366550
  have hstable : (prefixWord ++ tailWord_366550).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366550).length < 2 ^ (prefixWord ++ tailWord_366550).sum := by decide
  have hdescent : baseEnd_366550 < baseStart_366550 := by decide
  rcases family_descends (prefixWord ++ tailWord_366550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366724 : List Nat := [2, 3, 2, 1, 2, 1, 1, 1, 8]
def baseStart_366724 : Nat := 118140960795 + 366724 * 2 ^ 59
def prefixEnd_366724 : Nat := 4983230072969 + 3 ^ 40 * 366724 * 2
def baseEnd_366724 : Nat := 83691413128679299717099

theorem tailTrace_366724 : CollatzResearch.WordTrace tailWord_366724 prefixEnd_366724 83691413128679299717099 := by
  unfold tailWord_366724
  simp only [CollatzResearch.WordTrace]
  refine ⟨6687761561714527158981613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8917015415619369545308817 6687761561714527158981613)
  ·
    refine ⟨2507910585642947684618105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6687761561714527158981613 2507910585642947684618105)
    ·
      refine ⟨1880932939232210763463579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2507910585642947684618105 1880932939232210763463579)
      ·
        refine ⟨2821399408848316145195369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1880932939232210763463579 2821399408848316145195369)
        ·
          refine ⟨2116049556636237108896527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2821399408848316145195369 2116049556636237108896527)
          ·
            refine ⟨3174074334954355663344791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2116049556636237108896527 3174074334954355663344791)
            ·
              refine ⟨4761111502431533495017187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3174074334954355663344791 4761111502431533495017187)
              ·
                refine ⟨7141667253647300242525781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4761111502431533495017187 7141667253647300242525781)
                ·
                  refine ⟨83691413128679299717099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7141667253647300242525781 83691413128679299717099)
                  ·
                    rfl

theorem cell21_366724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_366724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_366724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_366724 prefixEnd_366724 := by exact prefixLift 366724
  have htrace : WordTrace (prefixWord ++ tailWord_366724) baseStart_366724 baseEnd_366724 := by
    simpa [prefixWord, tailWord_366724, baseEnd_366724] using wordTrace_append hprefix tailTrace_366724
  have hstable : (prefixWord ++ tailWord_366724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366724).length < 2 ^ (prefixWord ++ tailWord_366724).sum := by decide
  have hdescent : baseEnd_366724 < baseStart_366724 := by decide
  rcases family_descends (prefixWord ++ tailWord_366724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366727 : List Nat := [1, 1, 4, 2, 1, 1, 5, 3, 3]
def baseStart_366727 : Nat := 118140960795 + 366727 * 2 ^ 59
def prefixEnd_366727 : Nat := 4983230072969 + 3 ^ 40 * 366727 * 2
def baseEnd_366727 : Nat := 83692097769551961167093

theorem tailTrace_366727 : CollatzResearch.WordTrace tailWord_366727 prefixEnd_366727 83692097769551961167093 := by
  unfold tailWord_366727
  simp only [CollatzResearch.WordTrace]
  refine ⟨13375632542418185830322435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8917088361612123886881623 13375632542418185830322435)
  ·
    refine ⟨20063448813627278745483653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13375632542418185830322435 20063448813627278745483653)
    ·
      refine ⟨3761896652555114764778185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20063448813627278745483653 3761896652555114764778185)
      ·
        refine ⟨2821422489416336073583639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3761896652555114764778185 2821422489416336073583639)
        ·
          refine ⟨4232133734124504110375459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2821422489416336073583639 4232133734124504110375459)
          ·
            refine ⟨6348200601186756165563189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4232133734124504110375459 6348200601186756165563189)
            ·
              refine ⟨595143806361258390521549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6348200601186756165563189 595143806361258390521549)
              ·
                refine ⟨223178927385471896445581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 595143806361258390521549 223178927385471896445581)
                ·
                  refine ⟨83692097769551961167093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 223178927385471896445581 83692097769551961167093)
                  ·
                    rfl

theorem cell21_366727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 3, 3].length) (baseStart_366727 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_366727 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_366727 prefixEnd_366727 := by exact prefixLift 366727
  have htrace : WordTrace (prefixWord ++ tailWord_366727) baseStart_366727 baseEnd_366727 := by
    simpa [prefixWord, tailWord_366727, baseEnd_366727] using wordTrace_append hprefix tailTrace_366727
  have hstable : (prefixWord ++ tailWord_366727).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366727).length < 2 ^ (prefixWord ++ tailWord_366727).sum := by decide
  have hdescent : baseEnd_366727 < baseStart_366727 := by decide
  rcases family_descends (prefixWord ++ tailWord_366727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366744 : List Nat := [2, 1, 2, 4, 4, 1, 1, 1, 5]
def baseStart_366744 : Nat := 118140960795 + 366744 * 2 ^ 59
def prefixEnd_366744 : Nat := 4983230072969 + 3 ^ 40 * 366744 * 2
def baseEnd_366744 : Nat := 83695977401163709383725

theorem tailTrace_366744 : CollatzResearch.WordTrace tailWord_366744 prefixEnd_366744 83695977401163709383725 := by
  unfold tailWord_366744
  simp only [CollatzResearch.WordTrace]
  refine ⟨6688126291678298866845643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8917501722237731822460857 6688126291678298866845643)
  ·
    refine ⟨10032189437517448300268465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6688126291678298866845643 10032189437517448300268465)
    ·
      refine ⟨7524142078138086225201349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10032189437517448300268465 7524142078138086225201349)
      ·
        refine ⟨1410776639650891167225253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7524142078138086225201349 1410776639650891167225253)
        ·
          refine ⟨264520619934542093854735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1410776639650891167225253 264520619934542093854735)
          ·
            refine ⟨396780929901813140782103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264520619934542093854735 396780929901813140782103)
            ·
              refine ⟨595171394852719711173155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 396780929901813140782103 595171394852719711173155)
              ·
                refine ⟨892757092279079566759733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 595171394852719711173155 892757092279079566759733)
                ·
                  refine ⟨83695977401163709383725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 892757092279079566759733 83695977401163709383725)
                  ·
                    rfl

theorem cell21_366744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 1, 5].length) (baseStart_366744 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_366744 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_366744 prefixEnd_366744 := by exact prefixLift 366744
  have htrace : WordTrace (prefixWord ++ tailWord_366744) baseStart_366744 baseEnd_366744 := by
    simpa [prefixWord, tailWord_366744, baseEnd_366744] using wordTrace_append hprefix tailTrace_366744
  have hstable : (prefixWord ++ tailWord_366744).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366744).length < 2 ^ (prefixWord ++ tailWord_366744).sum := by decide
  have hdescent : baseEnd_366744 < baseStart_366744 := by decide
  rcases family_descends (prefixWord ++ tailWord_366744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366862 : List Nat := [4, 1, 1, 2, 1, 2, 4, 1, 5]
def baseStart_366862 : Nat := 118140960795 + 366862 * 2 ^ 59
def prefixEnd_366862 : Nat := 4983230072969 + 3 ^ 40 * 366862 * 2
def baseEnd_366862 : Nat := 83722906608821726416817

theorem tailTrace_366862 : CollatzResearch.WordTrace tailWord_366862 prefixEnd_366862 83722906608821726416817 := by
  unfold tailWord_366862
  simp only [CollatzResearch.WordTrace]
  refine ⟨1672569549616137985810855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8920370931286069257657893 1672569549616137985810855)
  ·
    refine ⟨2508854324424206978716283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1672569549616137985810855 2508854324424206978716283)
    ·
      refine ⟨3763281486636310468074425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2508854324424206978716283 3763281486636310468074425)
      ·
        refine ⟨2822461114977232851055819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3763281486636310468074425 2822461114977232851055819)
        ·
          refine ⟨4233691672465849276583729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2822461114977232851055819 4233691672465849276583729)
          ·
            refine ⟨3175268754349386957437797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4233691672465849276583729 3175268754349386957437797)
            ·
              refine ⟨595362891440510054519587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3175268754349386957437797 595362891440510054519587)
              ·
                refine ⟨893044337160765081779381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 595362891440510054519587 893044337160765081779381)
                ·
                  refine ⟨83722906608821726416817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 893044337160765081779381 83722906608821726416817)
                  ·
                    rfl

theorem cell21_366862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_366862 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_366862 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_366862 prefixEnd_366862 := by exact prefixLift 366862
  have htrace : WordTrace (prefixWord ++ tailWord_366862) baseStart_366862 baseEnd_366862 := by
    simpa [prefixWord, tailWord_366862, baseEnd_366862] using wordTrace_append hprefix tailTrace_366862
  have hstable : (prefixWord ++ tailWord_366862).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366862).length < 2 ^ (prefixWord ++ tailWord_366862).sum := by decide
  have hdescent : baseEnd_366862 < baseStart_366862 := by decide
  rcases family_descends (prefixWord ++ tailWord_366862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366913 : List Nat := [1, 2, 5, 2, 2, 1, 3, 2, 3]
def baseStart_366913 : Nat := 118140960795 + 366913 * 2 ^ 59
def prefixEnd_366913 : Nat := 4983230072969 + 3 ^ 40 * 366913 * 2
def baseEnd_366913 : Nat := 83734545503656971066713

theorem tailTrace_366913 : CollatzResearch.WordTrace tailWord_366913 prefixEnd_366913 83734545503656971066713 := by
  unfold tailWord_366913
  simp only [CollatzResearch.WordTrace]
  refine ⟨13382416519744339596593393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8921611013162893064395595 13382416519744339596593393)
  ·
    refine ⟨10036812389808254697445045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13382416519744339596593393 10036812389808254697445045)
    ·
      refine ⟨940951161544523877885473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10036812389808254697445045 940951161544523877885473)
      ·
        refine ⟨705713371158392908414105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 940951161544523877885473 705713371158392908414105)
        ·
          refine ⟨529285028368794681310579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 705713371158392908414105 529285028368794681310579)
          ·
            refine ⟨793927542553192021965869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 529285028368794681310579 793927542553192021965869)
            ·
              refine ⟨297722828457447008237201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 793927542553192021965869 297722828457447008237201)
              ·
                refine ⟨223292121343085256177901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 297722828457447008237201 223292121343085256177901)
                ·
                  refine ⟨83734545503656971066713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 223292121343085256177901 83734545503656971066713)
                  ·
                    rfl

theorem cell21_366913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3, 2, 3].length) (baseStart_366913 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_366913 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_366913 prefixEnd_366913 := by exact prefixLift 366913
  have htrace : WordTrace (prefixWord ++ tailWord_366913) baseStart_366913 baseEnd_366913 := by
    simpa [prefixWord, tailWord_366913, baseEnd_366913] using wordTrace_append hprefix tailTrace_366913
  have hstable : (prefixWord ++ tailWord_366913).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366913).length < 2 ^ (prefixWord ++ tailWord_366913).sum := by decide
  have hdescent : baseEnd_366913 < baseStart_366913 := by decide
  rcases family_descends (prefixWord ++ tailWord_366913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367000 : List Nat := [2, 1, 2, 5, 1, 2, 3, 5]
def baseStart_367000 : Nat := 118140960795 + 367000 * 2 ^ 59
def prefixEnd_367000 : Nat := 4983230072969 + 3 ^ 40 * 367000 * 2
def baseEnd_367000 : Nat := 27918133362988051038845

theorem tailTrace_367000 : CollatzResearch.WordTrace tailWord_367000 prefixEnd_367000 27918133362988051038845 := by
  unfold tailWord_367000
  simp only [CollatzResearch.WordTrace]
  refine ⟨6692794835214576727505227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8923726446952768970006969 6692794835214576727505227)
  ·
    refine ⟨10039192252821865091257841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6692794835214576727505227 10039192252821865091257841)
    ·
      refine ⟨7529394189616398818443381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10039192252821865091257841 7529394189616398818443381)
      ·
        refine ⟨705880705276537389229067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7529394189616398818443381 705880705276537389229067)
        ·
          refine ⟨1058821057914806083843601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 705880705276537389229067 1058821057914806083843601)
          ·
            refine ⟨794115793436104562882701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1058821057914806083843601 794115793436104562882701)
            ·
              refine ⟨297793422538539211081013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 794115793436104562882701 297793422538539211081013)
              ·
                refine ⟨27918133362988051038845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 297793422538539211081013 27918133362988051038845)
                ·
                  rfl

theorem cell21_367000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3, 5].length) (baseStart_367000 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_367000 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_367000 prefixEnd_367000 := by exact prefixLift 367000
  have htrace : WordTrace (prefixWord ++ tailWord_367000) baseStart_367000 baseEnd_367000 := by
    simpa [prefixWord, tailWord_367000, baseEnd_367000] using wordTrace_append hprefix tailTrace_367000
  have hstable : (prefixWord ++ tailWord_367000).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367000).length < 2 ^ (prefixWord ++ tailWord_367000).sum := by decide
  have hdescent : baseEnd_367000 < baseStart_367000 := by decide
  rcases family_descends (prefixWord ++ tailWord_367000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367214 : List Nat := [4, 1, 2, 2, 2, 2, 3, 1, 4]
def baseStart_367214 : Nat := 118140960795 + 367214 * 2 ^ 59
def prefixEnd_367214 : Nat := 4983230072969 + 3 ^ 40 * 367214 * 2
def baseEnd_367214 : Nat := 83803237804547336549431

theorem tailTrace_367214 : CollatzResearch.WordTrace tailWord_367214 prefixEnd_367214 83803237804547336549431 := by
  unfold tailWord_367214
  simp only [CollatzResearch.WordTrace]
  refine ⟨1674174361456733500412587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8928929927769245335533797 1674174361456733500412587)
  ·
    refine ⟨2511261542185100250618881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1674174361456733500412587 2511261542185100250618881)
    ·
      refine ⟨1883446156638825187964161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2511261542185100250618881 1883446156638825187964161)
      ·
        refine ⟨1412584617479118890973121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1883446156638825187964161 1412584617479118890973121)
        ·
          refine ⟨1059438463109339168229841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1412584617479118890973121 1059438463109339168229841)
          ·
            refine ⟨794578847332004376172381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1059438463109339168229841 794578847332004376172381)
            ·
              refine ⟨297967067749501641064643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 794578847332004376172381 297967067749501641064643)
              ·
                refine ⟨446950601624252461596965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 297967067749501641064643 446950601624252461596965)
                ·
                  refine ⟨83803237804547336549431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 446950601624252461596965 83803237804547336549431)
                  ·
                    rfl

theorem cell21_367214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3, 1, 4].length) (baseStart_367214 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_367214 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_367214 prefixEnd_367214 := by exact prefixLift 367214
  have htrace : WordTrace (prefixWord ++ tailWord_367214) baseStart_367214 baseEnd_367214 := by
    simpa [prefixWord, tailWord_367214, baseEnd_367214] using wordTrace_append hprefix tailTrace_367214
  have hstable : (prefixWord ++ tailWord_367214).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367214).length < 2 ^ (prefixWord ++ tailWord_367214).sum := by decide
  have hdescent : baseEnd_367214 < baseStart_367214 := by decide
  rcases family_descends (prefixWord ++ tailWord_367214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367225 : List Nat := [1, 2, 1, 3, 3, 2, 2, 2, 5]
def baseStart_367225 : Nat := 118140960795 + 367225 * 2 ^ 59
def prefixEnd_367225 : Nat := 4983230072969 + 3 ^ 40 * 367225 * 2
def baseEnd_367225 : Nat := 83805748154413761866075

theorem tailTrace_367225 : CollatzResearch.WordTrace tailWord_367225 prefixEnd_367225 83805748154413761866075 := by
  unfold tailWord_367225
  simp only [CollatzResearch.WordTrace]
  refine ⟨13393796094614016881951129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8929197396409344587967419 13393796094614016881951129)
  ·
    refine ⟨10045347070960512661463347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13393796094614016881951129 10045347070960512661463347)
    ·
      refine ⟨15068020606440768992195021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10045347070960512661463347 15068020606440768992195021)
      ·
        refine ⟨5650507727415288372073133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15068020606440768992195021 5650507727415288372073133)
        ·
          refine ⟨2118940397780733139527425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5650507727415288372073133 2118940397780733139527425)
          ·
            refine ⟨1589205298335549854645569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2118940397780733139527425 1589205298335549854645569)
            ·
              refine ⟨1191903973751662390984177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1589205298335549854645569 1191903973751662390984177)
              ·
                refine ⟨893927980313746793238133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1191903973751662390984177 893927980313746793238133)
                ·
                  refine ⟨83805748154413761866075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 893927980313746793238133 83805748154413761866075)
                  ·
                    rfl

theorem cell21_367225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 2, 5].length) (baseStart_367225 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_367225 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_367225 prefixEnd_367225 := by exact prefixLift 367225
  have htrace : WordTrace (prefixWord ++ tailWord_367225) baseStart_367225 baseEnd_367225 := by
    simpa [prefixWord, tailWord_367225, baseEnd_367225] using wordTrace_append hprefix tailTrace_367225
  have hstable : (prefixWord ++ tailWord_367225).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367225).length < 2 ^ (prefixWord ++ tailWord_367225).sum := by decide
  have hdescent : baseEnd_367225 < baseStart_367225 := by decide
  rcases family_descends (prefixWord ++ tailWord_367225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367239 : List Nat := [1, 1, 4, 2, 1, 2, 1, 1, 8]
def baseStart_367239 : Nat := 118140960795 + 367239 * 2 ^ 59
def prefixEnd_367239 : Nat := 4983230072969 + 3 ^ 40 * 367239 * 2
def baseEnd_367239 : Nat := 83808943145152848632713

theorem tailTrace_367239 : CollatzResearch.WordTrace tailWord_367239 prefixEnd_367239 83808943145152848632713 := by
  unfold tailWord_367239
  simp only [CollatzResearch.WordTrace]
  refine ⟨13394306716563297272960771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8929537811042198181973847 13394306716563297272960771)
  ·
    refine ⟨20091460074844945909441157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13394306716563297272960771 20091460074844945909441157)
    ·
      refine ⟨3767148764033427358020217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20091460074844945909441157 3767148764033427358020217)
      ·
        refine ⟨2825361573025070518515163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3767148764033427358020217 2825361573025070518515163)
        ·
          refine ⟨4238042359537605777772745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2825361573025070518515163 4238042359537605777772745)
          ·
            refine ⟨3178531769653204333329559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4238042359537605777772745 3178531769653204333329559)
            ·
              refine ⟨4767797654479806499994339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3178531769653204333329559 4767797654479806499994339)
              ·
                refine ⟨7151696481719709749991509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4767797654479806499994339 7151696481719709749991509)
                ·
                  refine ⟨83808943145152848632713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7151696481719709749991509 83808943145152848632713)
                  ·
                    rfl

theorem cell21_367239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 8].length) (baseStart_367239 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_367239 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_367239 prefixEnd_367239 := by exact prefixLift 367239
  have htrace : WordTrace (prefixWord ++ tailWord_367239) baseStart_367239 baseEnd_367239 := by
    simpa [prefixWord, tailWord_367239, baseEnd_367239] using wordTrace_append hprefix tailTrace_367239
  have hstable : (prefixWord ++ tailWord_367239).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367239).length < 2 ^ (prefixWord ++ tailWord_367239).sum := by decide
  have hdescent : baseEnd_367239 < baseStart_367239 := by decide
  rcases family_descends (prefixWord ++ tailWord_367239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367256 : List Nat := [2, 1, 2, 4, 1, 1, 2, 4, 4]
def baseStart_367256 : Nat := 118140960795 + 367256 * 2 ^ 59
def prefixEnd_367256 : Nat := 4983230072969 + 3 ^ 40 * 367256 * 2
def baseEnd_367256 : Nat := 83812822776764596849345

theorem tailTrace_367256 : CollatzResearch.WordTrace tailWord_367256 prefixEnd_367256 83812822776764596849345 := by
  unfold tailWord_367256
  simp only [CollatzResearch.WordTrace]
  refine ⟨6697463378750854588164811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8929951171667806117553081 6697463378750854588164811)
  ·
    refine ⟨10046195068126281882247217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6697463378750854588164811 10046195068126281882247217)
    ·
      refine ⟨7534646301094711411685413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10046195068126281882247217 7534646301094711411685413)
      ·
        refine ⟨1412746181455258389691015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7534646301094711411685413 1412746181455258389691015)
        ·
          refine ⟨2119119272182887584536523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1412746181455258389691015 2119119272182887584536523)
          ·
            refine ⟨3178678908274331376804785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2119119272182887584536523 3178678908274331376804785)
            ·
              refine ⟨2384009181205748532603589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3178678908274331376804785 2384009181205748532603589)
              ·
                refine ⟨447001721476077849863173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2384009181205748532603589 447001721476077849863173)
                ·
                  refine ⟨83812822776764596849345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 447001721476077849863173 83812822776764596849345)
                  ·
                    rfl

theorem cell21_367256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 4, 4].length) (baseStart_367256 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_367256 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_367256 prefixEnd_367256 := by exact prefixLift 367256
  have htrace : WordTrace (prefixWord ++ tailWord_367256) baseStart_367256 baseEnd_367256 := by
    simpa [prefixWord, tailWord_367256, baseEnd_367256] using wordTrace_append hprefix tailTrace_367256
  have hstable : (prefixWord ++ tailWord_367256).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367256).length < 2 ^ (prefixWord ++ tailWord_367256).sum := by decide
  have hdescent : baseEnd_367256 < baseStart_367256 := by decide
  rcases family_descends (prefixWord ++ tailWord_367256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367332 : List Nat := [2, 3, 1, 1, 1, 4, 2, 3, 4]
def baseStart_367332 : Nat := 118140960795 + 367332 * 2 ^ 59
def prefixEnd_367332 : Nat := 4983230072969 + 3 ^ 40 * 367332 * 2
def baseEnd_367332 : Nat := 83830167012205353582523

theorem tailTrace_367332 : CollatzResearch.WordTrace tailWord_367332 prefixEnd_367332 83830167012205353582523 := by
  unfold tailWord_367332
  simp only [CollatzResearch.WordTrace]
  refine ⟨6698849352613187078048125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8931799136817582770730833 6698849352613187078048125)
  ·
    refine ⟨2512068507229945154268047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6698849352613187078048125 2512068507229945154268047)
    ·
      refine ⟨3768102760844917731402071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2512068507229945154268047 3768102760844917731402071)
      ·
        refine ⟨5652154141267376597103107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3768102760844917731402071 5652154141267376597103107)
        ·
          refine ⟨8478231211901064895654661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5652154141267376597103107 8478231211901064895654661)
          ·
            refine ⟨1589668352231449667935249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8478231211901064895654661 1589668352231449667935249)
            ·
              refine ⟨1192251264173587250951437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1589668352231449667935249 1192251264173587250951437)
              ·
                refine ⟨447094224065095219106789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1192251264173587250951437 447094224065095219106789)
                ·
                  refine ⟨83830167012205353582523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 447094224065095219106789 83830167012205353582523)
                  ·
                    rfl

theorem cell21_367332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_367332 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_367332 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_367332 prefixEnd_367332 := by exact prefixLift 367332
  have htrace : WordTrace (prefixWord ++ tailWord_367332) baseStart_367332 baseEnd_367332 := by
    simpa [prefixWord, tailWord_367332, baseEnd_367332] using wordTrace_append hprefix tailTrace_367332
  have hstable : (prefixWord ++ tailWord_367332).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367332).length < 2 ^ (prefixWord ++ tailWord_367332).sum := by decide
  have hdescent : baseEnd_367332 < baseStart_367332 := by decide
  rcases family_descends (prefixWord ++ tailWord_367332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367411 : List Nat := [1, 1, 1, 2, 6, 3, 1, 3, 3]
def baseStart_367411 : Nat := 118140960795 + 367411 * 2 ^ 59
def prefixEnd_367411 : Nat := 4983230072969 + 3 ^ 40 * 367411 * 2
def baseEnd_367411 : Nat := 83848195888518771765695

theorem tailTrace_367411 : CollatzResearch.WordTrace tailWord_367411 prefixEnd_367411 83848195888518771765695 := by
  unfold tailWord_367411
  simp only [CollatzResearch.WordTrace]
  refine ⟨13400580071940170648222087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8933720047960113765481391 13400580071940170648222087)
  ·
    refine ⟨20100870107910255972333131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13400580071940170648222087 20100870107910255972333131)
    ·
      refine ⟨30151305161865383958499697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20100870107910255972333131 30151305161865383958499697)
      ·
        refine ⟨22613478871399037968874773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30151305161865383958499697 22613478871399037968874773)
        ·
          refine ⟨1060006822096829904791005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 22613478871399037968874773 1060006822096829904791005)
          ·
            refine ⟨397502558286311214296627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1060006822096829904791005 397502558286311214296627)
            ·
              refine ⟨596253837429466821444941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 397502558286311214296627 596253837429466821444941)
              ·
                refine ⟨223595189036050058041853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 596253837429466821444941 223595189036050058041853)
                ·
                  refine ⟨83848195888518771765695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 223595189036050058041853 83848195888518771765695)
                  ·
                    rfl

theorem cell21_367411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 3, 3].length) (baseStart_367411 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_367411 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_367411 prefixEnd_367411 := by exact prefixLift 367411
  have htrace : WordTrace (prefixWord ++ tailWord_367411) baseStart_367411 baseEnd_367411 := by
    simpa [prefixWord, tailWord_367411, baseEnd_367411] using wordTrace_append hprefix tailTrace_367411
  have hstable : (prefixWord ++ tailWord_367411).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367411).length < 2 ^ (prefixWord ++ tailWord_367411).sum := by decide
  have hdescent : baseEnd_367411 < baseStart_367411 := by decide
  rcases family_descends (prefixWord ++ tailWord_367411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367428 : List Nat := [2, 3, 4, 2, 1, 2, 1, 1, 5]
def baseStart_367428 : Nat := 118140960795 + 367428 * 2 ^ 59
def prefixEnd_367428 : Nat := 4983230072969 + 3 ^ 40 * 367428 * 2
def baseEnd_367428 : Nat := 83852075520130519982327

theorem tailTrace_367428 : CollatzResearch.WordTrace tailWord_367428 prefixEnd_367428 83852075520130519982327 := by
  unfold tailWord_367428
  simp only [CollatzResearch.WordTrace]
  refine ⟨6700600056439291275795469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8934133408585721701060625 6700600056439291275795469)
  ·
    refine ⟨2512725021164734228423301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6700600056439291275795469 2512725021164734228423301)
    ·
      refine ⟨471135941468387667829369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2512725021164734228423301 471135941468387667829369)
      ·
        refine ⟨353351956101290750872027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 471135941468387667829369 353351956101290750872027)
        ·
          refine ⟨530027934151936126308041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353351956101290750872027 530027934151936126308041)
          ·
            refine ⟨397520950613952094731031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 530027934151936126308041 397520950613952094731031)
            ·
              refine ⟨596281425920928142096547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 397520950613952094731031 596281425920928142096547)
              ·
                refine ⟨894422138881392213144821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 596281425920928142096547 894422138881392213144821)
                ·
                  refine ⟨83852075520130519982327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 894422138881392213144821 83852075520130519982327)
                  ·
                    rfl

theorem cell21_367428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 1, 5].length) (baseStart_367428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_367428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_367428 prefixEnd_367428 := by exact prefixLift 367428
  have htrace : WordTrace (prefixWord ++ tailWord_367428) baseStart_367428 baseEnd_367428 := by
    simpa [prefixWord, tailWord_367428, baseEnd_367428] using wordTrace_append hprefix tailTrace_367428
  have hstable : (prefixWord ++ tailWord_367428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367428).length < 2 ^ (prefixWord ++ tailWord_367428).sum := by decide
  have hdescent : baseEnd_367428 < baseStart_367428 := by decide
  rcases family_descends (prefixWord ++ tailWord_367428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367481 : List Nat := [1, 2, 1, 3, 2, 12]
def baseStart_367481 : Nat := 118140960795 + 367481 * 2 ^ 59
def prefixEnd_367481 : Nat := 4983230072969 + 3 ^ 40 * 367481 * 2
def baseEnd_367481 : Nat := 3106080401563489096255

theorem tailTrace_367481 : CollatzResearch.WordTrace tailWord_367481 prefixEnd_367481 3106080401563489096255 := by
  unfold tailWord_367481
  simp only [CollatzResearch.WordTrace]
  refine ⟨13403133181686572603270297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8935422121124381735513531 13403133181686572603270297)
  ·
    refine ⟨10052349886264929452452723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13403133181686572603270297 10052349886264929452452723)
    ·
      refine ⟨15078524829397394178679085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10052349886264929452452723 15078524829397394178679085)
      ·
        refine ⟨5654446811024022817004657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15078524829397394178679085 5654446811024022817004657)
        ·
          refine ⟨4240835108268017112753493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5654446811024022817004657 4240835108268017112753493)
          ·
            refine ⟨3106080401563489096255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 4240835108268017112753493 3106080401563489096255)
            ·
              rfl

theorem cell21_367481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 12].length) (baseStart_367481 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_367481 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_367481 prefixEnd_367481 := by exact prefixLift 367481
  have htrace : WordTrace (prefixWord ++ tailWord_367481) baseStart_367481 baseEnd_367481 := by
    simpa [prefixWord, tailWord_367481, baseEnd_367481] using wordTrace_append hprefix tailTrace_367481
  have hstable : (prefixWord ++ tailWord_367481).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367481).length < 2 ^ (prefixWord ++ tailWord_367481).sum := by decide
  have hdescent : baseEnd_367481 < baseStart_367481 := by decide
  rcases family_descends (prefixWord ++ tailWord_367481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367490 : List Nat := [3, 4, 2, 2, 2, 1, 1, 6]
def baseStart_367490 : Nat := 118140960795 + 367490 * 2 ^ 59
def prefixEnd_367490 : Nat := 4983230072969 + 3 ^ 40 * 367490 * 2
def baseEnd_367490 : Nat := 27955408254944063316289

theorem tailTrace_367490 : CollatzResearch.WordTrace tailWord_367490 prefixEnd_367490 27955408254944063316289 := by
  unfold tailWord_367490
  simp only [CollatzResearch.WordTrace]
  refine ⟨3350865359663491785086981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8935640959102644760231949 3350865359663491785086981)
  ·
    refine ⟨628287254936904709703809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3350865359663491785086981 628287254936904709703809)
    ·
      refine ⟨471215441202678532277857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 628287254936904709703809 471215441202678532277857)
      ·
        refine ⟨353411580902008899208393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 471215441202678532277857 353411580902008899208393)
        ·
          refine ⟨265058685676506674406295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 353411580902008899208393 265058685676506674406295)
          ·
            refine ⟨397588028514760011609443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265058685676506674406295 397588028514760011609443)
            ·
              refine ⟨596382042772140017414165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 397588028514760011609443 596382042772140017414165)
              ·
                refine ⟨27955408254944063316289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 596382042772140017414165 27955408254944063316289)
                ·
                  rfl

theorem cell21_367490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 6].length) (baseStart_367490 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_367490 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_367490 prefixEnd_367490 := by exact prefixLift 367490
  have htrace : WordTrace (prefixWord ++ tailWord_367490) baseStart_367490 baseEnd_367490 := by
    simpa [prefixWord, tailWord_367490, baseEnd_367490] using wordTrace_append hprefix tailTrace_367490
  have hstable : (prefixWord ++ tailWord_367490).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367490).length < 2 ^ (prefixWord ++ tailWord_367490).sum := by decide
  have hdescent : baseEnd_367490 < baseStart_367490 := by decide
  rcases family_descends (prefixWord ++ tailWord_367490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367664 : List Nat := [2, 1, 1, 1, 2, 4, 2, 3, 5]
def baseStart_367664 : Nat := 118140960795 + 367664 * 2 ^ 59
def prefixEnd_367664 : Nat := 4983230072969 + 3 ^ 40 * 367664 * 2
def baseEnd_367664 : Nat := 83905933935446554048511

theorem tailTrace_367664 : CollatzResearch.WordTrace tailWord_367664 prefixEnd_367664 83905933935446554048511 := by
  unfold tailWord_367664
  simp only [CollatzResearch.WordTrace]
  refine ⟨6704903870011797428591023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8939871826682396571454697 6704903870011797428591023)
  ·
    refine ⟨10057355805017696142886535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6704903870011797428591023 10057355805017696142886535)
    ·
      refine ⟨15086033707526544214329803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10057355805017696142886535 15086033707526544214329803)
      ·
        refine ⟨22629050561289816321494705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15086033707526544214329803 22629050561289816321494705)
        ·
          refine ⟨16971787920967362241121029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22629050561289816321494705 16971787920967362241121029)
          ·
            refine ⟨3182210235181380420210193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16971787920967362241121029 3182210235181380420210193)
            ·
              refine ⟨2386657676386035315157645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3182210235181380420210193 2386657676386035315157645)
              ·
                refine ⟨894996628644763243184117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2386657676386035315157645 894996628644763243184117)
                ·
                  refine ⟨83905933935446554048511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 894996628644763243184117 83905933935446554048511)
                  ·
                    rfl

theorem cell21_367664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3, 5].length) (baseStart_367664 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_367664 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_367664 prefixEnd_367664 := by exact prefixLift 367664
  have htrace : WordTrace (prefixWord ++ tailWord_367664) baseStart_367664 baseEnd_367664 := by
    simpa [prefixWord, tailWord_367664, baseEnd_367664] using wordTrace_append hprefix tailTrace_367664
  have hstable : (prefixWord ++ tailWord_367664).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367664).length < 2 ^ (prefixWord ++ tailWord_367664).sum := by decide
  have hdescent : baseEnd_367664 < baseStart_367664 := by decide
  rcases family_descends (prefixWord ++ tailWord_367664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367698 : List Nat := [3, 2, 2, 1, 3, 1, 1, 5, 3]
def baseStart_367698 : Nat := 118140960795 + 367698 * 2 ^ 59
def prefixEnd_367698 : Nat := 4983230072969 + 3 ^ 40 * 367698 * 2
def baseEnd_367698 : Nat := 83913693198670050481775

theorem tailTrace_367698 : CollatzResearch.WordTrace tailWord_367698 prefixEnd_367698 83913693198670050481775 := by
  unfold tailWord_367698
  simp only [CollatzResearch.WordTrace]
  refine ⟨3352761955475104665979937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8940698547933612442613165 3352761955475104665979937)
  ·
    refine ⟨2514571466606328499484953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3352761955475104665979937 2514571466606328499484953)
    ·
      refine ⟨1885928599954746374613715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2514571466606328499484953 1885928599954746374613715)
      ·
        refine ⟨2828892899932119561920573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1885928599954746374613715 2828892899932119561920573)
        ·
          refine ⟨1060834837474544835720215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2828892899932119561920573 1060834837474544835720215)
          ·
            refine ⟨1591252256211817253580323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1060834837474544835720215 1591252256211817253580323)
            ·
              refine ⟨2386878384317725880370485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1591252256211817253580323 2386878384317725880370485)
              ·
                refine ⟨223769848529786801284733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2386878384317725880370485 223769848529786801284733)
                ·
                  refine ⟨83913693198670050481775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 223769848529786801284733 83913693198670050481775)
                  ·
                    rfl

theorem cell21_367698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 5, 3].length) (baseStart_367698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_367698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_367698 prefixEnd_367698 := by exact prefixLift 367698
  have htrace : WordTrace (prefixWord ++ tailWord_367698) baseStart_367698 baseEnd_367698 := by
    simpa [prefixWord, tailWord_367698, baseEnd_367698] using wordTrace_append hprefix tailTrace_367698
  have hstable : (prefixWord ++ tailWord_367698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367698).length < 2 ^ (prefixWord ++ tailWord_367698).sum := by decide
  have hdescent : baseEnd_367698 < baseStart_367698 := by decide
  rcases family_descends (prefixWord ++ tailWord_367698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367740 : List Nat := [2, 2, 2, 1, 1, 3, 1, 4, 5]
def baseStart_367740 : Nat := 118140960795 + 367740 * 2 ^ 59
def prefixEnd_367740 : Nat := 4983230072969 + 3 ^ 40 * 367740 * 2
def baseEnd_367740 : Nat := 83923278170887310781689

theorem tailTrace_367740 : CollatzResearch.WordTrace tailWord_367740 prefixEnd_367740 83923278170887310781689 := by
  unfold tailWord_367740
  simp only [CollatzResearch.WordTrace]
  refine ⟨6706289843874129918474337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8941719791832173224632449 6706289843874129918474337)
  ·
    refine ⟨5029717382905597438855753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6706289843874129918474337 5029717382905597438855753)
    ·
      refine ⟨3772288037179198079141815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5029717382905597438855753 3772288037179198079141815)
      ·
        refine ⟨5658432055768797118712723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3772288037179198079141815 5658432055768797118712723)
        ·
          refine ⟨8487648083653195678069085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5658432055768797118712723 8487648083653195678069085)
          ·
            refine ⟨3182868031369948379275907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8487648083653195678069085 3182868031369948379275907)
            ·
              refine ⟨4774302047054922568913861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3182868031369948379275907 4774302047054922568913861)
              ·
                refine ⟨895181633822797981671349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4774302047054922568913861 895181633822797981671349)
                ·
                  refine ⟨83923278170887310781689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 895181633822797981671349 83923278170887310781689)
                  ·
                    rfl

theorem cell21_367740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4, 5].length) (baseStart_367740 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_367740 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_367740 prefixEnd_367740 := by exact prefixLift 367740
  have htrace : WordTrace (prefixWord ++ tailWord_367740) baseStart_367740 baseEnd_367740 := by
    simpa [prefixWord, tailWord_367740, baseEnd_367740] using wordTrace_append hprefix tailTrace_367740
  have hstable : (prefixWord ++ tailWord_367740).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367740).length < 2 ^ (prefixWord ++ tailWord_367740).sum := by decide
  have hdescent : baseEnd_367740 < baseStart_367740 := by decide
  rcases family_descends (prefixWord ++ tailWord_367740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367774 : List Nat := [4, 3, 1, 1, 2, 1, 3, 1, 5]
def baseStart_367774 : Nat := 118140960795 + 367774 * 2 ^ 59
def prefixEnd_367774 : Nat := 4983230072969 + 3 ^ 40 * 367774 * 2
def baseEnd_367774 : Nat := 83931037434110807214953

theorem tailTrace_367774 : CollatzResearch.WordTrace tailWord_367774 prefixEnd_367774 83931037434110807214953 := by
  unfold tailWord_367774
  simp only [CollatzResearch.WordTrace]
  refine ⟨1676727471203135455460797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8942546513083389095790917 1676727471203135455460797)
  ·
    refine ⟨628772801701175795797799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1676727471203135455460797 628772801701175795797799)
    ·
      refine ⟨943159202551763693696699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 628772801701175795797799 943159202551763693696699)
      ·
        refine ⟨1414738803827645540545049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 943159202551763693696699 1414738803827645540545049)
        ·
          refine ⟨1061054102870734155408787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1414738803827645540545049 1061054102870734155408787)
          ·
            refine ⟨1591581154306101233113181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1061054102870734155408787 1591581154306101233113181)
            ·
              refine ⟨596842932864787962417443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1591581154306101233113181 596842932864787962417443)
              ·
                refine ⟨895264399297181943626165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 596842932864787962417443 895264399297181943626165)
                ·
                  refine ⟨83931037434110807214953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 895264399297181943626165 83931037434110807214953)
                  ·
                    rfl

theorem cell21_367774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_367774 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_367774 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_367774 prefixEnd_367774 := by exact prefixLift 367774
  have htrace : WordTrace (prefixWord ++ tailWord_367774) baseStart_367774 baseEnd_367774 := by
    simpa [prefixWord, tailWord_367774, baseEnd_367774] using wordTrace_append hprefix tailTrace_367774
  have hstable : (prefixWord ++ tailWord_367774).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367774).length < 2 ^ (prefixWord ++ tailWord_367774).sum := by decide
  have hdescent : baseEnd_367774 < baseStart_367774 := by decide
  rcases family_descends (prefixWord ++ tailWord_367774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367940 : List Nat := [2, 3, 4, 1, 1, 1, 2, 1, 6]
def baseStart_367940 : Nat := 118140960795 + 367940 * 2 ^ 59
def prefixEnd_367940 : Nat := 4983230072969 + 3 ^ 40 * 367940 * 2
def baseEnd_367940 : Nat := 83968920895731407447947

theorem tailTrace_367940 : CollatzResearch.WordTrace tailWord_367940 prefixEnd_367940 83968920895731407447947 := by
  unfold tailWord_367940
  simp only [CollatzResearch.WordTrace]
  refine ⟨6709937143511846997114637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8946582858015795996152849 6709937143511846997114637)
  ·
    refine ⟨2516226428816942623917989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6709937143511846997114637 2516226428816942623917989)
    ·
      refine ⟨471792455403176741984623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2516226428816942623917989 471792455403176741984623)
      ·
        refine ⟨707688683104765112976935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 471792455403176741984623 707688683104765112976935)
        ·
          refine ⟨1061533024657147669465403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 707688683104765112976935 1061533024657147669465403)
          ·
            refine ⟨1592299536985721504198105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1061533024657147669465403 1592299536985721504198105)
            ·
              refine ⟨1194224652739291128148579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1592299536985721504198105 1194224652739291128148579)
              ·
                refine ⟨1791336979108936692222869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1194224652739291128148579 1791336979108936692222869)
                ·
                  refine ⟨83968920895731407447947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1791336979108936692222869 83968920895731407447947)
                  ·
                    rfl

theorem cell21_367940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_367940 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_367940 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_367940 prefixEnd_367940 := by exact prefixLift 367940
  have htrace : WordTrace (prefixWord ++ tailWord_367940) baseStart_367940 baseEnd_367940 := by
    simpa [prefixWord, tailWord_367940, baseEnd_367940] using wordTrace_append hprefix tailTrace_367940
  have hstable : (prefixWord ++ tailWord_367940).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367940).length < 2 ^ (prefixWord ++ tailWord_367940).sum := by decide
  have hdescent : baseEnd_367940 < baseStart_367940 := by decide
  rcases family_descends (prefixWord ++ tailWord_367940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367957 : List Nat := [1, 3, 2, 2, 3, 3, 2, 1, 4]
def baseStart_367957 : Nat := 118140960795 + 367957 * 2 ^ 59
def prefixEnd_367957 : Nat := 4983230072969 + 3 ^ 40 * 367957 * 2
def baseEnd_367957 : Nat := 83972800527343155664579

theorem tailTrace_367957 : CollatzResearch.WordTrace tailWord_367957 prefixEnd_367957 83972800527343155664579 := by
  unfold tailWord_367957
  simp only [CollatzResearch.WordTrace]
  refine ⟨13420494327962105897598125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8946996218641403931732083 13420494327962105897598125)
  ·
    refine ⟨5032685372985789711599297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13420494327962105897598125 5032685372985789711599297)
    ·
      refine ⟨3774514029739342283699473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5032685372985789711599297 3774514029739342283699473)
      ·
        refine ⟨2830885522304506712774605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3774514029739342283699473 2830885522304506712774605)
        ·
          refine ⟨1061582070864190017290477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2830885522304506712774605 1061582070864190017290477)
          ·
            refine ⟨398093276574071256483929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1061582070864190017290477 398093276574071256483929)
            ·
              refine ⟨298569957430553442362947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 398093276574071256483929 298569957430553442362947)
              ·
                refine ⟨447854936145830163544421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 298569957430553442362947 447854936145830163544421)
                ·
                  refine ⟨83972800527343155664579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 447854936145830163544421 83972800527343155664579)
                  ·
                    rfl

theorem cell21_367957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2, 1, 4].length) (baseStart_367957 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_367957 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_367957 prefixEnd_367957 := by exact prefixLift 367957
  have htrace : WordTrace (prefixWord ++ tailWord_367957) baseStart_367957 baseEnd_367957 := by
    simpa [prefixWord, tailWord_367957, baseEnd_367957] using wordTrace_append hprefix tailTrace_367957
  have hstable : (prefixWord ++ tailWord_367957).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367957).length < 2 ^ (prefixWord ++ tailWord_367957).sum := by decide
  have hdescent : baseEnd_367957 < baseStart_367957 := by decide
  rcases family_descends (prefixWord ++ tailWord_367957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368061 : List Nat := [1, 4, 1, 2, 2, 1, 1, 6, 3]
def baseStart_368061 : Nat := 118140960795 + 368061 * 2 ^ 59
def prefixEnd_368061 : Nat := 4983230072969 + 3 ^ 40 * 368061 * 2
def baseEnd_368061 : Nat := 83996534744262085931033

theorem tailTrace_368061 : CollatzResearch.WordTrace tailWord_368061 prefixEnd_368061 83996534744262085931033 := by
  unfold tailWord_368061
  simp only [CollatzResearch.WordTrace]
  refine ⟨13424287519585331659384037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8949525013056887772922691 13424287519585331659384037)
  ·
    refine ⟨2517053909922249686134507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13424287519585331659384037 2517053909922249686134507)
    ·
      refine ⟨3775580864883374529201761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2517053909922249686134507 3775580864883374529201761)
      ·
        refine ⟨2831685648662530896901321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3775580864883374529201761 2831685648662530896901321)
        ·
          refine ⟨2123764236496898172675991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2831685648662530896901321 2123764236496898172675991)
          ·
            refine ⟨3185646354745347259013987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2123764236496898172675991 3185646354745347259013987)
            ·
              refine ⟨4778469532118020888520981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3185646354745347259013987 4778469532118020888520981)
              ·
                refine ⟨223990759318032229149421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4778469532118020888520981 223990759318032229149421)
                ·
                  refine ⟨83996534744262085931033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 223990759318032229149421 83996534744262085931033)
                  ·
                    rfl

theorem cell21_368061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 6, 3].length) (baseStart_368061 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_368061 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_368061 prefixEnd_368061 := by exact prefixLift 368061
  have htrace : WordTrace (prefixWord ++ tailWord_368061) baseStart_368061 baseEnd_368061 := by
    simpa [prefixWord, tailWord_368061, baseEnd_368061] using wordTrace_append hprefix tailTrace_368061
  have hstable : (prefixWord ++ tailWord_368061).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368061).length < 2 ^ (prefixWord ++ tailWord_368061).sum := by decide
  have hdescent : baseEnd_368061 < baseStart_368061 := by decide
  rcases family_descends (prefixWord ++ tailWord_368061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368089 : List Nat := [1, 2, 1, 2, 4, 3, 1, 7]
def baseStart_368089 : Nat := 118140960795 + 368089 * 2 ^ 59
def prefixEnd_368089 : Nat := 4983230072969 + 3 ^ 40 * 368089 * 2
def baseEnd_368089 : Nat := 28000974908580086488103

theorem tailTrace_368089 : CollatzResearch.WordTrace tailWord_368089 prefixEnd_368089 28000974908580086488103 := by
  unfold tailWord_368089
  simp only [CollatzResearch.WordTrace]
  refine ⟨13425308763483892441403321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8950205842322594960935547 13425308763483892441403321)
  ·
    refine ⟨10068981572612919331052491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13425308763483892441403321 10068981572612919331052491)
    ·
      refine ⟨15103472358919378996578737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10068981572612919331052491 15103472358919378996578737)
      ·
        refine ⟨11327604269189534247434053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15103472358919378996578737 11327604269189534247434053)
        ·
          refine ⟨2123925800473037671393885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11327604269189534247434053 2123925800473037671393885)
          ·
            refine ⟨796472175177389126772707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2123925800473037671393885 796472175177389126772707)
            ·
              refine ⟨1194708262766083690159061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 796472175177389126772707 1194708262766083690159061)
              ·
                refine ⟨28000974908580086488103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1194708262766083690159061 28000974908580086488103)
                ·
                  rfl

theorem cell21_368089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 7].length) (baseStart_368089 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_368089 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_368089 prefixEnd_368089 := by exact prefixLift 368089
  have htrace : WordTrace (prefixWord ++ tailWord_368089) baseStart_368089 baseEnd_368089 := by
    simpa [prefixWord, tailWord_368089, baseEnd_368089] using wordTrace_append hprefix tailTrace_368089
  have hstable : (prefixWord ++ tailWord_368089).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368089).length < 2 ^ (prefixWord ++ tailWord_368089).sum := by decide
  have hdescent : baseEnd_368089 < baseStart_368089 := by decide
  rcases family_descends (prefixWord ++ tailWord_368089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368106 : List Nat := [3, 1, 3, 1, 4, 2, 7]
def baseStart_368106 : Nat := 118140960795 + 368106 * 2 ^ 59
def prefixEnd_368106 : Nat := 4983230072969 + 3 ^ 40 * 368106 * 2
def baseEnd_368106 : Nat := 9334089373039111964549

theorem tailTrace_368106 : CollatzResearch.WordTrace tailWord_368106 prefixEnd_368106 9334089373039111964549 := by
  unfold tailWord_368106
  simp only [CollatzResearch.WordTrace]
  refine ⟨3356482201105576086193043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8950619202948202896514781 3356482201105576086193043)
  ·
    refine ⟨5034723301658364129289565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3356482201105576086193043 5034723301658364129289565)
    ·
      refine ⟨1888021238121886548483587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5034723301658364129289565 1888021238121886548483587)
      ·
        refine ⟨2832031857182829822725381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1888021238121886548483587 2832031857182829822725381)
        ·
          refine ⟨531005973221780591761009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2832031857182829822725381 531005973221780591761009)
          ·
            refine ⟨398254479916335443820757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 531005973221780591761009 398254479916335443820757)
            ·
              refine ⟨9334089373039111964549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 398254479916335443820757 9334089373039111964549)
              ·
                rfl

theorem cell21_368106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 7].length) (baseStart_368106 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_368106 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_368106 prefixEnd_368106 := by exact prefixLift 368106
  have htrace : WordTrace (prefixWord ++ tailWord_368106) baseStart_368106 baseEnd_368106 := by
    simpa [prefixWord, tailWord_368106, baseEnd_368106] using wordTrace_append hprefix tailTrace_368106
  have hstable : (prefixWord ++ tailWord_368106).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368106).length < 2 ^ (prefixWord ++ tailWord_368106).sum := by decide
  have hdescent : baseEnd_368106 < baseStart_368106 := by decide
  rcases family_descends (prefixWord ++ tailWord_368106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368120 : List Nat := [2, 1, 2, 1, 1, 5, 3, 1, 5]
def baseStart_368120 : Nat := 118140960795 + 368120 * 2 ^ 59
def prefixEnd_368120 : Nat := 4983230072969 + 3 ^ 40 * 368120 * 2
def baseEnd_368120 : Nat := 84009999348091094447579

theorem tailTrace_368120 : CollatzResearch.WordTrace tailWord_368120 prefixEnd_368120 84009999348091094447579 := by
  unfold tailWord_368120
  simp only [CollatzResearch.WordTrace]
  refine ⟨6713219713185792367890907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8950959617581056490521209 6713219713185792367890907)
  ·
    refine ⟨10069829569778688551836361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6713219713185792367890907 10069829569778688551836361)
    ·
      refine ⟨7552372177334016413877271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10069829569778688551836361 7552372177334016413877271)
      ·
        refine ⟨11328558266001024620815907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7552372177334016413877271 11328558266001024620815907)
        ·
          refine ⟨16992837399001536931223861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11328558266001024620815907 16992837399001536931223861)
          ·
            refine ⟨1593078506156394087302237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16992837399001536931223861 1593078506156394087302237)
            ·
              refine ⟨597404439808647782738339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1593078506156394087302237 597404439808647782738339)
              ·
                refine ⟨896106659712971674107509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 597404439808647782738339 896106659712971674107509)
                ·
                  refine ⟨84009999348091094447579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 896106659712971674107509 84009999348091094447579)
                  ·
                    rfl

theorem cell21_368120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 1, 5].length) (baseStart_368120 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_368120 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_368120 prefixEnd_368120 := by exact prefixLift 368120
  have htrace : WordTrace (prefixWord ++ tailWord_368120) baseStart_368120 baseEnd_368120 := by
    simpa [prefixWord, tailWord_368120, baseEnd_368120] using wordTrace_append hprefix tailTrace_368120
  have hstable : (prefixWord ++ tailWord_368120).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368120).length < 2 ^ (prefixWord ++ tailWord_368120).sum := by decide
  have hdescent : baseEnd_368120 < baseStart_368120 := by decide
  rcases family_descends (prefixWord ++ tailWord_368120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368227 : List Nat := [1, 1, 1, 5, 1, 3, 3, 2, 4]
def baseStart_368227 : Nat := 118140960795 + 368227 * 2 ^ 59
def prefixEnd_368227 : Nat := 4983230072969 + 3 ^ 40 * 368227 * 2
def baseEnd_368227 : Nat := 84034418205882686164027

theorem tailTrace_368227 : CollatzResearch.WordTrace tailWord_368227 prefixEnd_368227 84034418205882686164027 := by
  unfold tailWord_368227
  simp only [CollatzResearch.WordTrace]
  refine ⟨13430342036983942009926935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8953561357989294673284623 13430342036983942009926935)
  ·
    refine ⟨20145513055475913014890403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13430342036983942009926935 20145513055475913014890403)
    ·
      refine ⟨30218269583213869522335605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20145513055475913014890403 30218269583213869522335605)
      ·
        refine ⟨2832962773426300267718963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30218269583213869522335605 2832962773426300267718963)
        ·
          refine ⟨4249444160139450401578445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2832962773426300267718963 4249444160139450401578445)
          ·
            refine ⟨1593541560052293900591917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4249444160139450401578445 1593541560052293900591917)
            ·
              refine ⟨597578085019610212721969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1593541560052293900591917 597578085019610212721969)
              ·
                refine ⟨448183563764707659541477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 597578085019610212721969 448183563764707659541477)
                ·
                  refine ⟨84034418205882686164027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 448183563764707659541477 84034418205882686164027)
                  ·
                    rfl

theorem cell21_368227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 2, 4].length) (baseStart_368227 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_368227 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_368227 prefixEnd_368227 := by exact prefixLift 368227
  have htrace : WordTrace (prefixWord ++ tailWord_368227) baseStart_368227 baseEnd_368227 := by
    simpa [prefixWord, tailWord_368227, baseEnd_368227] using wordTrace_append hprefix tailTrace_368227
  have hstable : (prefixWord ++ tailWord_368227).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368227).length < 2 ^ (prefixWord ++ tailWord_368227).sum := by decide
  have hdescent : baseEnd_368227 < baseStart_368227 := by decide
  rcases family_descends (prefixWord ++ tailWord_368227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368264 : List Nat := [2, 1, 3, 5, 2, 1, 1, 3, 3]
def baseStart_368264 : Nat := 118140960795 + 368264 * 2 ^ 59
def prefixEnd_368264 : Nat := 4983230072969 + 3 ^ 40 * 368264 * 2
def baseEnd_368264 : Nat := 84042862109978844047285

theorem tailTrace_368264 : CollatzResearch.WordTrace tailWord_368264 prefixEnd_368264 84042862109978844047285 := by
  unfold tailWord_368264
  simp only [CollatzResearch.WordTrace]
  refine ⟨6715845768924948664511923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8954461025233264886015897 6715845768924948664511923)
  ·
    refine ⟨10073768653387422996767885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6715845768924948664511923 10073768653387422996767885)
    ·
      refine ⟨3777663245020283623787957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10073768653387422996767885 3777663245020283623787957)
      ·
        refine ⟨354155929220651589730121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3777663245020283623787957 354155929220651589730121)
        ·
          refine ⟨265616946915488692297591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 354155929220651589730121 265616946915488692297591)
          ·
            refine ⟨398425420373233038446387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265616946915488692297591 398425420373233038446387)
            ·
              refine ⟨597638130559849557669581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 398425420373233038446387 597638130559849557669581)
              ·
                refine ⟨224114298959943584126093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 597638130559849557669581 224114298959943584126093)
                ·
                  refine ⟨84042862109978844047285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 224114298959943584126093 84042862109978844047285)
                  ·
                    rfl

theorem cell21_368264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 3, 3].length) (baseStart_368264 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_368264 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_368264 prefixEnd_368264 := by exact prefixLift 368264
  have htrace : WordTrace (prefixWord ++ tailWord_368264) baseStart_368264 baseEnd_368264 := by
    simpa [prefixWord, tailWord_368264, baseEnd_368264] using wordTrace_append hprefix tailTrace_368264
  have hstable : (prefixWord ++ tailWord_368264).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368264).length < 2 ^ (prefixWord ++ tailWord_368264).sum := by decide
  have hdescent : baseEnd_368264 < baseStart_368264 := by decide
  rcases family_descends (prefixWord ++ tailWord_368264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368289 : List Nat := [1, 2, 3, 3, 2, 3, 1, 1, 5]
def baseStart_368289 : Nat := 118140960795 + 368289 * 2 ^ 59
def prefixEnd_368289 : Nat := 4983230072969 + 3 ^ 40 * 368289 * 2
def baseEnd_368289 : Nat := 84048567450584356130567

theorem tailTrace_368289 : CollatzResearch.WordTrace tailWord_368289 prefixEnd_368289 84048567450584356130567 := by
  unfold tailWord_368289
  simp only [CollatzResearch.WordTrace]
  refine ⟨13432603362759326598683921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8955068908506217732455947 13432603362759326598683921)
  ·
    refine ⟨10074452522069494949012941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13432603362759326598683921 10074452522069494949012941)
    ·
      refine ⟨3777919695776060605879853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10074452522069494949012941 3777919695776060605879853)
      ·
        refine ⟨1416719885916022727204945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3777919695776060605879853 1416719885916022727204945)
        ·
          refine ⟨1062539914437017045403709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1416719885916022727204945 1062539914437017045403709)
          ·
            refine ⟨398452467913881392026391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1062539914437017045403709 398452467913881392026391)
            ·
              refine ⟨597678701870822088039587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 398452467913881392026391 597678701870822088039587)
              ·
                refine ⟨896518052806233132059381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 597678701870822088039587 896518052806233132059381)
                ·
                  refine ⟨84048567450584356130567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 896518052806233132059381 84048567450584356130567)
                  ·
                    rfl

theorem cell21_368289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 1, 5].length) (baseStart_368289 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_368289 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_368289 prefixEnd_368289 := by exact prefixLift 368289
  have htrace : WordTrace (prefixWord ++ tailWord_368289) baseStart_368289 baseEnd_368289 := by
    simpa [prefixWord, tailWord_368289, baseEnd_368289] using wordTrace_append hprefix tailTrace_368289
  have hstable : (prefixWord ++ tailWord_368289).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368289).length < 2 ^ (prefixWord ++ tailWord_368289).sum := by decide
  have hdescent : baseEnd_368289 < baseStart_368289 := by decide
  rcases family_descends (prefixWord ++ tailWord_368289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368424 : List Nat := [2, 1, 5, 1, 1, 2, 2, 2, 5]
def baseStart_368424 : Nat := 118140960795 + 368424 * 2 ^ 59
def prefixEnd_368424 : Nat := 4983230072969 + 3 ^ 40 * 368424 * 2
def baseEnd_368424 : Nat := 84079376289854121380291

theorem tailTrace_368424 : CollatzResearch.WordTrace tailWord_368424 prefixEnd_368424 84079376289854121380291 := by
  unfold tailWord_368424
  simp only [CollatzResearch.WordTrace]
  refine ⟨6718763608635122327424163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8958351478180163103232217 6718763608635122327424163)
  ·
    refine ⟨10078145412952683491136245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6718763608635122327424163 10078145412952683491136245)
    ·
      refine ⟨944826132464314077294023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10078145412952683491136245 944826132464314077294023)
      ·
        refine ⟨1417239198696471115941035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 944826132464314077294023 1417239198696471115941035)
        ·
          refine ⟨2125858798044706673911553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1417239198696471115941035 2125858798044706673911553)
          ·
            refine ⟨1594394098533530005433665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2125858798044706673911553 1594394098533530005433665)
            ·
              refine ⟨1195795573900147504075249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1594394098533530005433665 1195795573900147504075249)
              ·
                refine ⟨896846680425110628056437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1195795573900147504075249 896846680425110628056437)
                ·
                  refine ⟨84079376289854121380291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 896846680425110628056437 84079376289854121380291)
                  ·
                    rfl

theorem cell21_368424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 2, 5].length) (baseStart_368424 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_368424 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_368424 prefixEnd_368424 := by exact prefixLift 368424
  have htrace : WordTrace (prefixWord ++ tailWord_368424) baseStart_368424 baseEnd_368424 := by
    simpa [prefixWord, tailWord_368424, baseEnd_368424] using wordTrace_append hprefix tailTrace_368424
  have hstable : (prefixWord ++ tailWord_368424).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368424).length < 2 ^ (prefixWord ++ tailWord_368424).sum := by decide
  have hdescent : baseEnd_368424 < baseStart_368424 := by decide
  rcases family_descends (prefixWord ++ tailWord_368424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368469 : List Nat := [1, 3, 2, 2, 2, 3, 2, 6]
def baseStart_368469 : Nat := 118140960795 + 368469 * 2 ^ 59
def prefixEnd_368469 : Nat := 4983230072969 + 3 ^ 40 * 368469 * 2
def baseEnd_368469 : Nat := 28029881967648014376733

theorem tailTrace_368469 : CollatzResearch.WordTrace tailWord_368469 prefixEnd_368469 28029881967648014376733 := by
  unfold tailWord_368469
  simp only [CollatzResearch.WordTrace]
  refine ⟨13439168502107217340236461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8959445668071478226824307 13439168502107217340236461)
  ·
    refine ⟨5039688188290206502588673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13439168502107217340236461 5039688188290206502588673)
    ·
      refine ⟨3779766141217654876941505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5039688188290206502588673 3779766141217654876941505)
      ·
        refine ⟨2834824605913241157706129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3779766141217654876941505 2834824605913241157706129)
        ·
          refine ⟨2126118454434930868279597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2834824605913241157706129 2126118454434930868279597)
          ·
            refine ⟨797294420413099075604849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2126118454434930868279597 797294420413099075604849)
            ·
              refine ⟨597970815309824306703637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 797294420413099075604849 597970815309824306703637)
              ·
                refine ⟨28029881967648014376733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 597970815309824306703637 28029881967648014376733)
                ·
                  rfl

theorem cell21_368469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 6].length) (baseStart_368469 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_368469 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_368469 prefixEnd_368469 := by exact prefixLift 368469
  have htrace : WordTrace (prefixWord ++ tailWord_368469) baseStart_368469 baseEnd_368469 := by
    simpa [prefixWord, tailWord_368469, baseEnd_368469] using wordTrace_append hprefix tailTrace_368469
  have hstable : (prefixWord ++ tailWord_368469).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368469).length < 2 ^ (prefixWord ++ tailWord_368469).sum := by decide
  have hdescent : baseEnd_368469 < baseStart_368469 := by decide
  rcases family_descends (prefixWord ++ tailWord_368469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368576 : List Nat := [2, 1, 1, 2, 3, 2, 1, 6, 3]
def baseStart_368576 : Nat := 118140960795 + 368576 * 2 ^ 59
def prefixEnd_368576 : Nat := 4983230072969 + 3 ^ 40 * 368576 * 2
def baseEnd_368576 : Nat := 84114064760735634846647

theorem tailTrace_368576 : CollatzResearch.WordTrace tailWord_368576 prefixEnd_368576 84114064760735634846647 := by
  unfold tailWord_368576
  simp only [CollatzResearch.WordTrace]
  refine ⟨6721535556359787307190791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8962047408479716409587721 6721535556359787307190791)
  ·
    refine ⟨10082303334539680960786187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6721535556359787307190791 10082303334539680960786187)
    ·
      refine ⟨15123455001809521441179281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10082303334539680960786187 15123455001809521441179281)
      ·
        refine ⟨11342591251357141080884461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15123455001809521441179281 11342591251357141080884461)
        ·
          refine ⟨4253471719258927905331673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11342591251357141080884461 4253471719258927905331673)
          ·
            refine ⟨3190103789444195928998755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4253471719258927905331673 3190103789444195928998755)
            ·
              refine ⟨4785155684166293893498133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3190103789444195928998755 4785155684166293893498133)
              ·
                refine ⟨224304172695295026257725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4785155684166293893498133 224304172695295026257725)
                ·
                  refine ⟨84114064760735634846647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 224304172695295026257725 84114064760735634846647)
                  ·
                    rfl

theorem cell21_368576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 6, 3].length) (baseStart_368576 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_368576 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_368576 prefixEnd_368576 := by exact prefixLift 368576
  have htrace : WordTrace (prefixWord ++ tailWord_368576) baseStart_368576 baseEnd_368576 := by
    simpa [prefixWord, tailWord_368576, baseEnd_368576] using wordTrace_append hprefix tailTrace_368576
  have hstable : (prefixWord ++ tailWord_368576).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368576).length < 2 ^ (prefixWord ++ tailWord_368576).sum := by decide
  have hdescent : baseEnd_368576 < baseStart_368576 := by decide
  rcases family_descends (prefixWord ++ tailWord_368576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368635 : List Nat := [1, 1, 1, 1, 1, 3, 7, 1, 5]
def baseStart_368635 : Nat := 118140960795 + 368635 * 2 ^ 59
def prefixEnd_368635 : Nat := 4983230072969 + 3 ^ 40 * 368635 * 2
def baseEnd_368635 : Nat := 84127529364564643363193

theorem tailTrace_368635 : CollatzResearch.WordTrace tailWord_368635 prefixEnd_368635 84127529364564643363193 := by
  unfold tailWord_368635
  simp only [CollatzResearch.WordTrace]
  refine ⟨13445223019505827690779359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8963482013003885127186239 13445223019505827690779359)
  ·
    refine ⟨20167834529258741536169039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13445223019505827690779359 20167834529258741536169039)
    ·
      refine ⟨30251751793888112304253559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20167834529258741536169039 30251751793888112304253559)
      ·
        refine ⟨45377627690832168456380339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30251751793888112304253559 45377627690832168456380339)
        ·
          refine ⟨68066441536248252684570509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45377627690832168456380339 68066441536248252684570509)
          ·
            refine ⟨25524915576093094756713941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68066441536248252684570509 25524915576093094756713941)
            ·
              refine ⟨598240208814681908360483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 25524915576093094756713941 598240208814681908360483)
              ·
                refine ⟨897360313222022862540725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 598240208814681908360483 897360313222022862540725)
                ·
                  refine ⟨84127529364564643363193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 897360313222022862540725 84127529364564643363193)
                  ·
                    rfl

theorem cell21_368635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 1, 5].length) (baseStart_368635 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_368635 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_368635 prefixEnd_368635 := by exact prefixLift 368635
  have htrace : WordTrace (prefixWord ++ tailWord_368635) baseStart_368635 baseEnd_368635 := by
    simpa [prefixWord, tailWord_368635, baseEnd_368635] using wordTrace_append hprefix tailTrace_368635
  have hstable : (prefixWord ++ tailWord_368635).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368635).length < 2 ^ (prefixWord ++ tailWord_368635).sum := by decide
  have hdescent : baseEnd_368635 < baseStart_368635 := by decide
  rcases family_descends (prefixWord ++ tailWord_368635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368638 : List Nat := [4, 2, 2, 2, 1, 2, 2, 6]
def baseStart_368638 : Nat := 118140960795 + 368638 * 2 ^ 59
def prefixEnd_368638 : Nat := 4983230072969 + 3 ^ 40 * 368638 * 2
def baseEnd_368638 : Nat := 28042738001812434937729

theorem tailTrace_368638 : CollatzResearch.WordTrace tailWord_368638 prefixEnd_368638 28042738001812434937729 := by
  unfold tailWord_368638
  simp only [CollatzResearch.WordTrace]
  refine ⟨1680666554811869900392321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8963554958996639468759045 1680666554811869900392321)
  ·
    refine ⟨1260499916108902425294241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1680666554811869900392321 1260499916108902425294241)
    ·
      refine ⟨945374937081676818970681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1260499916108902425294241 945374937081676818970681)
      ·
        refine ⟨709031202811257614228011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 945374937081676818970681 709031202811257614228011)
        ·
          refine ⟨1063546804216886421342017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 709031202811257614228011 1063546804216886421342017)
          ·
            refine ⟨797660103162664816006513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1063546804216886421342017 797660103162664816006513)
            ·
              refine ⟨598245077371998612004885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 797660103162664816006513 598245077371998612004885)
              ·
                refine ⟨28042738001812434937729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 598245077371998612004885 28042738001812434937729)
                ·
                  rfl

theorem cell21_368638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 6].length) (baseStart_368638 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_368638 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_368638 prefixEnd_368638 := by exact prefixLift 368638
  have htrace : WordTrace (prefixWord ++ tailWord_368638) baseStart_368638 baseEnd_368638 := by
    simpa [prefixWord, tailWord_368638, baseEnd_368638] using wordTrace_append hprefix tailTrace_368638
  have hstable : (prefixWord ++ tailWord_368638).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368638).length < 2 ^ (prefixWord ++ tailWord_368638).sum := by decide
  have hdescent : baseEnd_368638 < baseStart_368638 := by decide
  rcases family_descends (prefixWord ++ tailWord_368638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368686 : List Nat := [4, 1, 3, 1, 1, 2, 4, 2, 3]
def baseStart_368686 : Nat := 118140960795 + 368686 * 2 ^ 59
def prefixEnd_368686 : Nat := 4983230072969 + 3 ^ 40 * 368686 * 2
def baseEnd_368686 : Nat := 84139168259399888013089

theorem tailTrace_368686 : CollatzResearch.WordTrace tailWord_368686 prefixEnd_368686 84139168259399888013089 := by
  unfold tailWord_368686
  simp only [CollatzResearch.WordTrace]
  refine ⟨1680885392790132925110739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8964722094880708933923941 1680885392790132925110739)
  ·
    refine ⟨2521328089185199387666109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1680885392790132925110739 2521328089185199387666109)
    ·
      refine ⟨945498033444449770374791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2521328089185199387666109 945498033444449770374791)
      ·
        refine ⟨1418247050166674655562187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 945498033444449770374791 1418247050166674655562187)
        ·
          refine ⟨2127370575250011983343281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1418247050166674655562187 2127370575250011983343281)
          ·
            refine ⟨1595527931437508987507461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2127370575250011983343281 1595527931437508987507461)
            ·
              refine ⟨299161487144532935157649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1595527931437508987507461 299161487144532935157649)
              ·
                refine ⟨224371115358399701368237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 299161487144532935157649 224371115358399701368237)
                ·
                  refine ⟨84139168259399888013089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 224371115358399701368237 84139168259399888013089)
                  ·
                    rfl

theorem cell21_368686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4, 2, 3].length) (baseStart_368686 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_368686 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_368686 prefixEnd_368686 := by exact prefixLift 368686
  have htrace : WordTrace (prefixWord ++ tailWord_368686) baseStart_368686 baseEnd_368686 := by
    simpa [prefixWord, tailWord_368686, baseEnd_368686] using wordTrace_append hprefix tailTrace_368686
  have hstable : (prefixWord ++ tailWord_368686).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368686).length < 2 ^ (prefixWord ++ tailWord_368686).sum := by decide
  have hdescent : baseEnd_368686 < baseStart_368686 := by decide
  rcases family_descends (prefixWord ++ tailWord_368686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368711 : List Nat := [1, 1, 4, 1, 3, 1, 3, 2, 5]
def baseStart_368711 : Nat := 118140960795 + 368711 * 2 ^ 59
def prefixEnd_368711 : Nat := 4983230072969 + 3 ^ 40 * 368711 * 2
def baseEnd_368711 : Nat := 84144873600005400096371

theorem tailTrace_368711 : CollatzResearch.WordTrace tailWord_368711 prefixEnd_368711 84144873600005400096371 := by
  unfold tailWord_368711
  simp only [CollatzResearch.WordTrace]
  refine ⟨13447994967230492670545987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8965329978153661780363991 13447994967230492670545987)
  ·
    refine ⟨20171992450845739005818981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13447994967230492670545987 20171992450845739005818981)
    ·
      refine ⟨3782248584533576063591059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20171992450845739005818981 3782248584533576063591059)
      ·
        refine ⟨5673372876800364095386589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3782248584533576063591059 5673372876800364095386589)
        ·
          refine ⟨2127514828800136535769971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5673372876800364095386589 2127514828800136535769971)
          ·
            refine ⟨3191272243200204803654957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2127514828800136535769971 3191272243200204803654957)
            ·
              refine ⟨1196727091200076801370609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3191272243200204803654957 1196727091200076801370609)
              ·
                refine ⟨897545318400057601027957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1196727091200076801370609 897545318400057601027957)
                ·
                  refine ⟨84144873600005400096371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 897545318400057601027957 84144873600005400096371)
                  ·
                    rfl

theorem cell21_368711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 2, 5].length) (baseStart_368711 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_368711 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_368711 prefixEnd_368711 := by exact prefixLift 368711
  have htrace : WordTrace (prefixWord ++ tailWord_368711) baseStart_368711 baseEnd_368711 := by
    simpa [prefixWord, tailWord_368711, baseEnd_368711] using wordTrace_append hprefix tailTrace_368711
  have hstable : (prefixWord ++ tailWord_368711).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368711).length < 2 ^ (prefixWord ++ tailWord_368711).sum := by decide
  have hdescent : baseEnd_368711 < baseStart_368711 := by decide
  rcases family_descends (prefixWord ++ tailWord_368711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368728 : List Nat := [2, 1, 2, 2, 1, 4, 1, 5, 3]
def baseStart_368728 : Nat := 118140960795 + 368728 * 2 ^ 59
def prefixEnd_368728 : Nat := 4983230072969 + 3 ^ 40 * 368728 * 2
def baseEnd_368728 : Nat := 84148753231617148313003

theorem tailTrace_368728 : CollatzResearch.WordTrace tailWord_368728 prefixEnd_368728 84148753231617148313003 := by
  unfold tailWord_368728
  simp only [CollatzResearch.WordTrace]
  refine ⟨6724307504084452286957419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8965743338779269715943225 6724307504084452286957419)
  ·
    refine ⟨10086461256126678430436129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6724307504084452286957419 10086461256126678430436129)
    ·
      refine ⟨7564845942095008822827097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10086461256126678430436129 7564845942095008822827097)
      ·
        refine ⟨5673634456571256617120323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7564845942095008822827097 5673634456571256617120323)
        ·
          refine ⟨8510451684856884925680485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5673634456571256617120323 8510451684856884925680485)
          ·
            refine ⟨1595709690910665923565091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8510451684856884925680485 1595709690910665923565091)
            ·
              refine ⟨2393564536365998885347637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1595709690910665923565091 2393564536365998885347637)
              ·
                refine ⟨224396675284312395501341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2393564536365998885347637 224396675284312395501341)
                ·
                  refine ⟨84148753231617148313003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 224396675284312395501341 84148753231617148313003)
                  ·
                    rfl

theorem cell21_368728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 5, 3].length) (baseStart_368728 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_368728 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_368728 prefixEnd_368728 := by exact prefixLift 368728
  have htrace : WordTrace (prefixWord ++ tailWord_368728) baseStart_368728 baseEnd_368728 := by
    simpa [prefixWord, tailWord_368728, baseEnd_368728] using wordTrace_append hprefix tailTrace_368728
  have hstable : (prefixWord ++ tailWord_368728).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368728).length < 2 ^ (prefixWord ++ tailWord_368728).sum := by decide
  have hdescent : baseEnd_368728 < baseStart_368728 := by decide
  rcases family_descends (prefixWord ++ tailWord_368728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368734 : List Nat := [4, 4, 1, 1, 2, 2, 1, 2, 4]
def baseStart_368734 : Nat := 118140960795 + 368734 * 2 ^ 59
def prefixEnd_368734 : Nat := 4983230072969 + 3 ^ 40 * 368734 * 2
def baseEnd_368734 : Nat := 84150122513362471212991

theorem tailTrace_368734 : CollatzResearch.WordTrace tailWord_368734 prefixEnd_368734 84150122513362471212991 := by
  unfold tailWord_368734
  simp only [CollatzResearch.WordTrace]
  refine ⟨1681104230768395949829157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8965889230764778399088837 1681104230768395949829157)
  ·
    refine ⟨315207043269074240592967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1681104230768395949829157 315207043269074240592967)
    ·
      refine ⟨472810564903611360889451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315207043269074240592967 472810564903611360889451)
      ·
        refine ⟨709215847355417041334177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 472810564903611360889451 709215847355417041334177)
        ·
          refine ⟨531911885516562781000633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 709215847355417041334177 531911885516562781000633)
          ·
            refine ⟨398933914137422085750475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 531911885516562781000633 398933914137422085750475)
            ·
              refine ⟨598400871206133128625713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 398933914137422085750475 598400871206133128625713)
              ·
                refine ⟨448800653404599846469285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 598400871206133128625713 448800653404599846469285)
                ·
                  refine ⟨84150122513362471212991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 448800653404599846469285 84150122513362471212991)
                  ·
                    rfl

theorem cell21_368734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_368734 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_368734 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_368734 prefixEnd_368734 := by exact prefixLift 368734
  have htrace : WordTrace (prefixWord ++ tailWord_368734) baseStart_368734 baseEnd_368734 := by
    simpa [prefixWord, tailWord_368734, baseEnd_368734] using wordTrace_append hprefix tailTrace_368734
  have hstable : (prefixWord ++ tailWord_368734).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368734).length < 2 ^ (prefixWord ++ tailWord_368734).sum := by decide
  have hdescent : baseEnd_368734 < baseStart_368734 := by decide
  rcases family_descends (prefixWord ++ tailWord_368734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368759 : List Nat := [1, 1, 3, 1, 1, 6, 3, 1, 4]
def baseStart_368759 : Nat := 118140960795 + 368759 * 2 ^ 59
def prefixEnd_368759 : Nat := 4983230072969 + 3 ^ 40 * 368759 * 2
def baseEnd_368759 : Nat := 84155827853967983296273

theorem tailTrace_368759 : CollatzResearch.WordTrace tailWord_368759 prefixEnd_368759 84155827853967983296273 := by
  unfold tailWord_368759
  simp only [CollatzResearch.WordTrace]
  refine ⟨13449745671056596868293331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8966497114037731245528887 13449745671056596868293331)
  ·
    refine ⟨20174618506584895302439997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13449745671056596868293331 20174618506584895302439997)
    ·
      refine ⟨7565481939969335738414999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20174618506584895302439997 7565481939969335738414999)
      ·
        refine ⟨11348222909954003607622499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7565481939969335738414999 11348222909954003607622499)
        ·
          refine ⟨17022334364931005411433749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11348222909954003607622499 17022334364931005411433749)
          ·
            refine ⟨797921923356140878660957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17022334364931005411433749 797921923356140878660957)
            ·
              refine ⟨299220721258552829497859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 797921923356140878660957 299220721258552829497859)
              ·
                refine ⟨448831081887829244246789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 299220721258552829497859 448831081887829244246789)
                ·
                  refine ⟨84155827853967983296273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 448831081887829244246789 84155827853967983296273)
                  ·
                    rfl

theorem cell21_368759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3, 1, 4].length) (baseStart_368759 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_368759 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_368759 prefixEnd_368759 := by exact prefixLift 368759
  have htrace : WordTrace (prefixWord ++ tailWord_368759) baseStart_368759 baseEnd_368759 := by
    simpa [prefixWord, tailWord_368759, baseEnd_368759] using wordTrace_append hprefix tailTrace_368759
  have hstable : (prefixWord ++ tailWord_368759).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368759).length < 2 ^ (prefixWord ++ tailWord_368759).sum := by decide
  have hdescent : baseEnd_368759 < baseStart_368759 := by decide
  rcases family_descends (prefixWord ++ tailWord_368759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368773 : List Nat := [1, 3, 1, 1, 5, 1, 4, 5]
def baseStart_368773 : Nat := 118140960795 + 368773 * 2 ^ 59
def prefixEnd_368773 : Nat := 4983230072969 + 3 ^ 40 * 368773 * 2
def baseEnd_368773 : Nat := 28053007614902356687637

theorem tailTrace_368773 : CollatzResearch.WordTrace tailWord_368773 prefixEnd_368773 28053007614902356687637 := by
  unfold tailWord_368773
  simp only [CollatzResearch.WordTrace]
  refine ⟨13450256293005877259302973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8966837528670584839535315 13450256293005877259302973)
  ·
    refine ⟨5043846109877203972238615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13450256293005877259302973 5043846109877203972238615)
    ·
      refine ⟨7565769164815805958357923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5043846109877203972238615 7565769164815805958357923)
      ·
        refine ⟨11348653747223708937536885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7565769164815805958357923 11348653747223708937536885)
        ·
          refine ⟨1063936288802222712894083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11348653747223708937536885 1063936288802222712894083)
          ·
            refine ⟨1595904433203334069341125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1063936288802222712894083 1595904433203334069341125)
            ·
              refine ⟨299232081225625138001461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1595904433203334069341125 299232081225625138001461)
              ·
                refine ⟨28053007614902356687637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 299232081225625138001461 28053007614902356687637)
                ·
                  rfl

theorem cell21_368773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4, 5].length) (baseStart_368773 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_368773 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_368773 prefixEnd_368773 := by exact prefixLift 368773
  have htrace : WordTrace (prefixWord ++ tailWord_368773) baseStart_368773 baseEnd_368773 := by
    simpa [prefixWord, tailWord_368773, baseEnd_368773] using wordTrace_append hprefix tailTrace_368773
  have hstable : (prefixWord ++ tailWord_368773).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368773).length < 2 ^ (prefixWord ++ tailWord_368773).sum := by decide
  have hdescent : baseEnd_368773 < baseStart_368773 := by decide
  rcases family_descends (prefixWord ++ tailWord_368773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368810 : List Nat := [3, 1, 5, 1, 3, 1, 2, 1, 4]
def baseStart_368810 : Nat := 118140960795 + 368810 * 2 ^ 59
def prefixEnd_368810 : Nat := 4983230072969 + 3 ^ 40 * 368810 * 2
def baseEnd_368810 : Nat := 84167466748803227946169

theorem tailTrace_368810 : CollatzResearch.WordTrace tailWord_368810 prefixEnd_368810 84167466748803227946169 := by
  unfold tailWord_368810
  simp only [CollatzResearch.WordTrace]
  refine ⟨3362901448467958144599971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8967737195914555052266589 3362901448467958144599971)
  ·
    refine ⟨5044352172701937216899957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3362901448467958144599971 5044352172701937216899957)
    ·
      refine ⟨472908016190806614084371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5044352172701937216899957 472908016190806614084371)
      ·
        refine ⟨709362024286209921126557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 472908016190806614084371 709362024286209921126557)
        ·
          refine ⟨266010759107328720422459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 709362024286209921126557 266010759107328720422459)
          ·
            refine ⟨399016138660993080633689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266010759107328720422459 399016138660993080633689)
            ·
              refine ⟨299262103995744810475267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 399016138660993080633689 299262103995744810475267)
              ·
                refine ⟨448893155993617215712901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 299262103995744810475267 448893155993617215712901)
                ·
                  refine ⟨84167466748803227946169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 448893155993617215712901 84167466748803227946169)
                  ·
                    rfl

theorem cell21_368810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 2, 1, 4].length) (baseStart_368810 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_368810 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_368810 prefixEnd_368810 := by exact prefixLift 368810
  have htrace : WordTrace (prefixWord ++ tailWord_368810) baseStart_368810 baseEnd_368810 := by
    simpa [prefixWord, tailWord_368810, baseEnd_368810] using wordTrace_append hprefix tailTrace_368810
  have hstable : (prefixWord ++ tailWord_368810).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368810).length < 2 ^ (prefixWord ++ tailWord_368810).sum := by decide
  have hdescent : baseEnd_368810 < baseStart_368810 := by decide
  rcases family_descends (prefixWord ++ tailWord_368810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368818 : List Nat := [3, 2, 1, 1, 1, 3, 3, 3, 4]
def baseStart_368818 : Nat := 118140960795 + 368818 * 2 ^ 59
def prefixEnd_368818 : Nat := 4983230072969 + 3 ^ 40 * 368818 * 2
def baseEnd_368818 : Nat := 84169292457796991812819

theorem tailTrace_368818 : CollatzResearch.WordTrace tailWord_368818 prefixEnd_368818 84169292457796991812819 := by
  unfold tailWord_368818
  simp only [CollatzResearch.WordTrace]
  refine ⟨3362974394460712486172777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8967931718561899963127405 3362974394460712486172777)
  ·
    refine ⟨2522230795845534364629583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3362974394460712486172777 2522230795845534364629583)
    ·
      refine ⟨3783346193768301546944375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2522230795845534364629583 3783346193768301546944375)
      ·
        refine ⟨5675019290652452320416563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3783346193768301546944375 5675019290652452320416563)
        ·
          refine ⟨8512528935978678480624845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5675019290652452320416563 8512528935978678480624845)
          ·
            refine ⟨3192198350992004430234317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8512528935978678480624845 3192198350992004430234317)
            ·
              refine ⟨1197074381622001661337869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3192198350992004430234317 1197074381622001661337869)
              ·
                refine ⟨448902893108250623001701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1197074381622001661337869 448902893108250623001701)
                ·
                  refine ⟨84169292457796991812819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 448902893108250623001701 84169292457796991812819)
                  ·
                    rfl

theorem cell21_368818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_368818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_368818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_368818 prefixEnd_368818 := by exact prefixLift 368818
  have htrace : WordTrace (prefixWord ++ tailWord_368818) baseStart_368818 baseEnd_368818 := by
    simpa [prefixWord, tailWord_368818, baseEnd_368818] using wordTrace_append hprefix tailTrace_368818
  have hstable : (prefixWord ++ tailWord_368818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368818).length < 2 ^ (prefixWord ++ tailWord_368818).sum := by decide
  have hdescent : baseEnd_368818 < baseStart_368818 := by decide
  rcases family_descends (prefixWord ++ tailWord_368818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368832 : List Nat := [2, 1, 1, 2, 5, 1, 2, 7]
def baseStart_368832 : Nat := 118140960795 + 368832 * 2 ^ 59
def prefixEnd_368832 : Nat := 4983230072969 + 3 ^ 40 * 368832 * 2
def baseEnd_368832 : Nat := 28057495816178692859819

theorem tailTrace_368832 : CollatzResearch.WordTrace tailWord_368832 prefixEnd_368832 28057495816178692859819 := by
  unfold tailWord_368832
  simp only [CollatzResearch.WordTrace]
  refine ⟨6726204099896065167850375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8968272133194753557133833 6726204099896065167850375)
  ·
    refine ⟨10089306149844097751775563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6726204099896065167850375 10089306149844097751775563)
    ·
      refine ⟨15133959224766146627663345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10089306149844097751775563 15133959224766146627663345)
      ·
        refine ⟨11350469418574609970747509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15133959224766146627663345 11350469418574609970747509)
        ·
          refine ⟨1064106507991369684757579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11350469418574609970747509 1064106507991369684757579)
          ·
            refine ⟨1596159761987054527136369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1064106507991369684757579 1596159761987054527136369)
            ·
              refine ⟨1197119821490290895352277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1596159761987054527136369 1197119821490290895352277)
              ·
                refine ⟨28057495816178692859819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1197119821490290895352277 28057495816178692859819)
                ·
                  rfl

theorem cell21_368832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 7].length) (baseStart_368832 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_368832 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_368832 prefixEnd_368832 := by exact prefixLift 368832
  have htrace : WordTrace (prefixWord ++ tailWord_368832) baseStart_368832 baseEnd_368832 := by
    simpa [prefixWord, tailWord_368832, baseEnd_368832] using wordTrace_append hprefix tailTrace_368832
  have hstable : (prefixWord ++ tailWord_368832).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368832).length < 2 ^ (prefixWord ++ tailWord_368832).sum := by decide
  have hdescent : baseEnd_368832 < baseStart_368832 := by decide
  rcases family_descends (prefixWord ++ tailWord_368832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368894 : List Nat := [4, 2, 2, 1, 1, 1, 2, 2, 6]
def baseStart_368894 : Nat := 118140960795 + 368894 * 2 ^ 59
def prefixEnd_368894 : Nat := 4983230072969 + 3 ^ 40 * 368894 * 2
def baseEnd_368894 : Nat := 84186636693237748545997

theorem tailTrace_368894 : CollatzResearch.WordTrace tailWord_368894 prefixEnd_368894 84186636693237748545997 := by
  unfold tailWord_368894
  simp only [CollatzResearch.WordTrace]
  refine ⟨1681833690695939365557217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8969779683711676616305157 1681833690695939365557217)
  ·
    refine ⟨1261375268021954524167913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1681833690695939365557217 1261375268021954524167913)
    ·
      refine ⟨946031451016465893125935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1261375268021954524167913 946031451016465893125935)
      ·
        refine ⟨1419047176524698839688903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 946031451016465893125935 1419047176524698839688903)
        ·
          refine ⟨2128570764787048259533355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1419047176524698839688903 2128570764787048259533355)
          ·
            refine ⟨3192856147180572389300033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2128570764787048259533355 3192856147180572389300033)
            ·
              refine ⟨2394642110385429291975025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3192856147180572389300033 2394642110385429291975025)
              ·
                refine ⟨1795981582789071968981269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2394642110385429291975025 1795981582789071968981269)
                ·
                  refine ⟨84186636693237748545997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1795981582789071968981269 84186636693237748545997)
                  ·
                    rfl

theorem cell21_368894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_368894 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_368894 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_368894 prefixEnd_368894 := by exact prefixLift 368894
  have htrace : WordTrace (prefixWord ++ tailWord_368894) baseStart_368894 baseEnd_368894 := by
    simpa [prefixWord, tailWord_368894, baseEnd_368894] using wordTrace_append hprefix tailTrace_368894
  have hstable : (prefixWord ++ tailWord_368894).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368894).length < 2 ^ (prefixWord ++ tailWord_368894).sum := by decide
  have hdescent : baseEnd_368894 < baseStart_368894 := by decide
  rcases family_descends (prefixWord ++ tailWord_368894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368942 : List Nat := [4, 1, 3, 3, 1, 1, 1, 7]
def baseStart_368942 : Nat := 118140960795 + 368942 * 2 ^ 59
def prefixEnd_368942 : Nat := 4983230072969 + 3 ^ 40 * 368942 * 2
def baseEnd_368942 : Nat := 28065863649066777248633

theorem tailTrace_368942 : CollatzResearch.WordTrace tailWord_368942 prefixEnd_368942 28065863649066777248633 := by
  unfold tailWord_368942
  simp only [CollatzResearch.WordTrace]
  refine ⟨1682052528674202390275635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8970946819595746081470053 1682052528674202390275635)
  ·
    refine ⟨2523078793011303585413453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1682052528674202390275635 2523078793011303585413453)
    ·
      refine ⟨946154547379238844530045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2523078793011303585413453 946154547379238844530045)
      ·
        refine ⟨354807955267214566698767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 946154547379238844530045 354807955267214566698767)
        ·
          refine ⟨532211932900821850048151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 354807955267214566698767 532211932900821850048151)
          ·
            refine ⟨798317899351232775072227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 532211932900821850048151 798317899351232775072227)
            ·
              refine ⟨1197476849026849162608341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 798317899351232775072227 1197476849026849162608341)
              ·
                refine ⟨28065863649066777248633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1197476849026849162608341 28065863649066777248633)
                ·
                  rfl

theorem cell21_368942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 7].length) (baseStart_368942 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_368942 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_368942 prefixEnd_368942 := by exact prefixLift 368942
  have htrace : WordTrace (prefixWord ++ tailWord_368942) baseStart_368942 baseEnd_368942 := by
    simpa [prefixWord, tailWord_368942, baseEnd_368942] using wordTrace_append hprefix tailTrace_368942
  have hstable : (prefixWord ++ tailWord_368942).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368942).length < 2 ^ (prefixWord ++ tailWord_368942).sum := by decide
  have hdescent : baseEnd_368942 < baseStart_368942 := by decide
  rcases family_descends (prefixWord ++ tailWord_368942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369032 : List Nat := [2, 1, 3, 3, 1, 1, 3, 4, 3]
def baseStart_369032 : Nat := 118140960795 + 369032 * 2 ^ 59
def prefixEnd_369032 : Nat := 4983230072969 + 3 ^ 40 * 369032 * 2
def baseEnd_369032 : Nat := 84218130173380175245715

theorem tailTrace_369032 : CollatzResearch.WordTrace tailWord_369032 prefixEnd_369032 84218130173380175245715 := by
  unfold tailWord_369032
  simp only [CollatzResearch.WordTrace]
  refine ⟨6729851399533782246490675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8973135199378376328654233 6729851399533782246490675)
  ·
    refine ⟨10094777099300673369736013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6729851399533782246490675 10094777099300673369736013)
    ·
      refine ⟨3785541412237752513651005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10094777099300673369736013 3785541412237752513651005)
      ·
        refine ⟨1419578029589157192619127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3785541412237752513651005 1419578029589157192619127)
        ·
          refine ⟨2129367044383735788928691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1419578029589157192619127 2129367044383735788928691)
          ·
            refine ⟨3194050566575603683393037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2129367044383735788928691 3194050566575603683393037)
            ·
              refine ⟨1197768962465851381272389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3194050566575603683393037 1197768962465851381272389)
              ·
                refine ⟨224581680462347133988573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1197768962465851381272389 224581680462347133988573)
                ·
                  refine ⟨84218130173380175245715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 224581680462347133988573 84218130173380175245715)
                  ·
                    rfl

theorem cell21_369032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 4, 3].length) (baseStart_369032 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_369032 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_369032 prefixEnd_369032 := by exact prefixLift 369032
  have htrace : WordTrace (prefixWord ++ tailWord_369032) baseStart_369032 baseEnd_369032 := by
    simpa [prefixWord, tailWord_369032, baseEnd_369032] using wordTrace_append hprefix tailTrace_369032
  have hstable : (prefixWord ++ tailWord_369032).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369032).length < 2 ^ (prefixWord ++ tailWord_369032).sum := by decide
  have hdescent : baseEnd_369032 < baseStart_369032 := by decide
  rcases family_descends (prefixWord ++ tailWord_369032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369074 : List Nat := [3, 2, 1, 1, 1, 1, 3, 2, 7]
def baseStart_369074 : Nat := 118140960795 + 369074 * 2 ^ 59
def prefixEnd_369074 : Nat := 4983230072969 + 3 ^ 40 * 369074 * 2
def baseEnd_369074 : Nat := 84227715145597435545629

theorem tailTrace_369074 : CollatzResearch.WordTrace tailWord_369074 prefixEnd_369074 84227715145597435545629 := by
  unfold tailWord_369074
  simp only [CollatzResearch.WordTrace]
  refine ⟨3365308666228851416502569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8974156443276937110673517 3365308666228851416502569)
  ·
    refine ⟨2523981499671638562376927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3365308666228851416502569 2523981499671638562376927)
    ·
      refine ⟨3785972249507457843565391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2523981499671638562376927 3785972249507457843565391)
      ·
        refine ⟨5678958374261186765348087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3785972249507457843565391 5678958374261186765348087)
        ·
          refine ⟨8518437561391780148022131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5678958374261186765348087 8518437561391780148022131)
          ·
            refine ⟨12777656342087670222033197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8518437561391780148022131 12777656342087670222033197)
            ·
              refine ⟨4791621128282876333262449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12777656342087670222033197 4791621128282876333262449)
              ·
                refine ⟨3593715846212157249946837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4791621128282876333262449 3593715846212157249946837)
                ·
                  refine ⟨84227715145597435545629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3593715846212157249946837 84227715145597435545629)
                  ·
                    rfl

theorem cell21_369074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_369074 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_369074 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_369074 prefixEnd_369074 := by exact prefixLift 369074
  have htrace : WordTrace (prefixWord ++ tailWord_369074) baseStart_369074 baseEnd_369074 := by
    simpa [prefixWord, tailWord_369074, baseEnd_369074] using wordTrace_append hprefix tailTrace_369074
  have hstable : (prefixWord ++ tailWord_369074).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369074).length < 2 ^ (prefixWord ++ tailWord_369074).sum := by decide
  have hdescent : baseEnd_369074 < baseStart_369074 := by decide
  rcases family_descends (prefixWord ++ tailWord_369074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369105 : List Nat := [1, 2, 2, 1, 2, 1, 1, 7, 4]
def baseStart_369105 : Nat := 118140960795 + 369105 * 2 ^ 59
def prefixEnd_369105 : Nat := 4983230072969 + 3 ^ 40 * 369105 * 2
def baseEnd_369105 : Nat := 84234789767948270528899

theorem tailTrace_369105 : CollatzResearch.WordTrace tailWord_369105 prefixEnd_369105 84234789767948270528899 := by
  unfold tailWord_369105
  simp only [CollatzResearch.WordTrace]
  refine ⟨13462365327803097960388769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8974910218535398640259179 13462365327803097960388769)
  ·
    refine ⟨10096773995852323470291577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13462365327803097960388769 10096773995852323470291577)
    ·
      refine ⟨7572580496889242602718683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10096773995852323470291577 7572580496889242602718683)
      ·
        refine ⟨11358870745333863904078025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7572580496889242602718683 11358870745333863904078025)
        ·
          refine ⟨8519153059000397928058519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11358870745333863904078025 8519153059000397928058519)
          ·
            refine ⟨12778729588500596892087779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8519153059000397928058519 12778729588500596892087779)
            ·
              refine ⟨19168094382750895338131669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12778729588500596892087779 19168094382750895338131669)
              ·
                refine ⟨449252212095724109487461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 19168094382750895338131669 449252212095724109487461)
                ·
                  refine ⟨84234789767948270528899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 449252212095724109487461 84234789767948270528899)
                  ·
                    rfl

theorem cell21_369105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 7, 4].length) (baseStart_369105 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_369105 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_369105 prefixEnd_369105 := by exact prefixLift 369105
  have htrace : WordTrace (prefixWord ++ tailWord_369105) baseStart_369105 baseEnd_369105 := by
    simpa [prefixWord, tailWord_369105, baseEnd_369105] using wordTrace_append hprefix tailTrace_369105
  have hstable : (prefixWord ++ tailWord_369105).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369105).length < 2 ^ (prefixWord ++ tailWord_369105).sum := by decide
  have hdescent : baseEnd_369105 < baseStart_369105 := by decide
  rcases family_descends (prefixWord ++ tailWord_369105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369156 : List Nat := [2, 3, 2, 3, 1, 3, 2, 1, 4]
def baseStart_369156 : Nat := 118140960795 + 369156 * 2 ^ 59
def prefixEnd_369156 : Nat := 4983230072969 + 3 ^ 40 * 369156 * 2
def baseEnd_369156 : Nat := 84246428662783515178795

theorem tailTrace_369156 : CollatzResearch.WordTrace tailWord_369156 prefixEnd_369156 84246428662783515178795 := by
  unfold tailWord_369156
  simp only [CollatzResearch.WordTrace]
  refine ⟨6732112725309166835247661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8976150300412222446996881 6732112725309166835247661)
  ·
    refine ⟨2524542271990937563217873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6732112725309166835247661 2524542271990937563217873)
    ·
      refine ⟨1893406703993203172413405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2524542271990937563217873 1893406703993203172413405)
      ·
        refine ⟨710027513997451189655027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1893406703993203172413405 710027513997451189655027)
        ·
          refine ⟨1065041270996176784482541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 710027513997451189655027 1065041270996176784482541)
          ·
            refine ⟨399390476623566294180953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1065041270996176784482541 399390476623566294180953)
            ·
              refine ⟨299542857467674720635715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 399390476623566294180953 299542857467674720635715)
              ·
                refine ⟨449314286201512080953573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 299542857467674720635715 449314286201512080953573)
                ·
                  refine ⟨84246428662783515178795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 449314286201512080953573 84246428662783515178795)
                  ·
                    rfl

theorem cell21_369156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2, 1, 4].length) (baseStart_369156 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_369156 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_369156 prefixEnd_369156 := by exact prefixLift 369156
  have htrace : WordTrace (prefixWord ++ tailWord_369156) baseStart_369156 baseEnd_369156 := by
    simpa [prefixWord, tailWord_369156, baseEnd_369156] using wordTrace_append hprefix tailTrace_369156
  have hstable : (prefixWord ++ tailWord_369156).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369156).length < 2 ^ (prefixWord ++ tailWord_369156).sum := by decide
  have hdescent : baseEnd_369156 < baseStart_369156 := by decide
  rcases family_descends (prefixWord ++ tailWord_369156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369212 : List Nat := [2, 2, 2, 2, 3, 1, 3, 6]
def baseStart_369212 : Nat := 118140960795 + 369212 * 2 ^ 59
def prefixEnd_369212 : Nat := 4983230072969 + 3 ^ 40 * 369212 * 2
def baseEnd_369212 : Nat := 28086402875246620748449

theorem tailTrace_369212 : CollatzResearch.WordTrace tailWord_369212 prefixEnd_369212 28086402875246620748449 := by
  unfold tailWord_369212
  simp only [CollatzResearch.WordTrace]
  refine ⟨6733133969207727617266945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8977511958943636823022593 6733133969207727617266945)
  ·
    refine ⟨5049850476905795712950209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6733133969207727617266945 5049850476905795712950209)
    ·
      refine ⟨3787387857679346784712657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5049850476905795712950209 3787387857679346784712657)
      ·
        refine ⟨2840540893259510088534493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3787387857679346784712657 2840540893259510088534493)
        ·
          refine ⟨1065202834972316283200435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2840540893259510088534493 1065202834972316283200435)
          ·
            refine ⟨1597804252458474424800653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1065202834972316283200435 1597804252458474424800653)
            ·
              refine ⟨599176594671927909300245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1597804252458474424800653 599176594671927909300245)
              ·
                refine ⟨28086402875246620748449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 599176594671927909300245 28086402875246620748449)
                ·
                  rfl

theorem cell21_369212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 6].length) (baseStart_369212 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_369212 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_369212 prefixEnd_369212 := by exact prefixLift 369212
  have htrace : WordTrace (prefixWord ++ tailWord_369212) baseStart_369212 baseEnd_369212 := by
    simpa [prefixWord, tailWord_369212, baseEnd_369212] using wordTrace_append hprefix tailTrace_369212
  have hstable : (prefixWord ++ tailWord_369212).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369212).length < 2 ^ (prefixWord ++ tailWord_369212).sum := by decide
  have hdescent : baseEnd_369212 < baseStart_369212 := by decide
  rcases family_descends (prefixWord ++ tailWord_369212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369226 : List Nat := [3, 1, 2, 1, 1, 4, 1, 1, 7]
def baseStart_369226 : Nat := 118140960795 + 369226 * 2 ^ 59
def prefixEnd_369226 : Nat := 4983230072969 + 3 ^ 40 * 369226 * 2
def baseEnd_369226 : Nat := 84262403616478949011985

theorem tailTrace_369226 : CollatzResearch.WordTrace tailWord_369226 prefixEnd_369226 84262403616478949011985 := by
  unfold tailWord_369226
  simp only [CollatzResearch.WordTrace]
  refine ⟨3366694640091183906385883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8977852373576490417029021 3366694640091183906385883)
  ·
    refine ⟨5050041960136775859578825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3366694640091183906385883 5050041960136775859578825)
    ·
      refine ⟨3787531470102581894684119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5050041960136775859578825 3787531470102581894684119)
      ·
        refine ⟨5681297205153872842026179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3787531470102581894684119 5681297205153872842026179)
        ·
          refine ⟨8521945807730809263039269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5681297205153872842026179 8521945807730809263039269)
          ·
            refine ⟨1597864838949526736819863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8521945807730809263039269 1597864838949526736819863)
            ·
              refine ⟨2396797258424290105229795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1597864838949526736819863 2396797258424290105229795)
              ·
                refine ⟨3595195887636435157844693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2396797258424290105229795 3595195887636435157844693)
                ·
                  refine ⟨84262403616478949011985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3595195887636435157844693 84262403616478949011985)
                  ·
                    rfl

theorem cell21_369226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 7].length) (baseStart_369226 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_369226 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_369226 prefixEnd_369226 := by exact prefixLift 369226
  have htrace : WordTrace (prefixWord ++ tailWord_369226) baseStart_369226 baseEnd_369226 := by
    simpa [prefixWord, tailWord_369226, baseEnd_369226] using wordTrace_append hprefix tailTrace_369226
  have hstable : (prefixWord ++ tailWord_369226).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369226).length < 2 ^ (prefixWord ++ tailWord_369226).sum := by decide
  have hdescent : baseEnd_369226 < baseStart_369226 := by decide
  rcases family_descends (prefixWord ++ tailWord_369226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369322 : List Nat := [3, 1, 5, 2, 1, 1, 2, 6]
def baseStart_369322 : Nat := 118140960795 + 369322 * 2 ^ 59
def prefixEnd_369322 : Nat := 4983230072969 + 3 ^ 40 * 369322 * 2
def baseEnd_369322 : Nat := 28094770708134705137263

theorem tailTrace_369322 : CollatzResearch.WordTrace tailWord_369322 prefixEnd_369322 28094770708134705137263 := by
  unfold tailWord_369322
  simp only [CollatzResearch.WordTrace]
  refine ⟨3367569992004236005259555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8980186645344629347358813 3367569992004236005259555)
  ·
    refine ⟨5051354988006354007889333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3367569992004236005259555 5051354988006354007889333)
    ·
      refine ⟨473564530125595688239625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5051354988006354007889333 473564530125595688239625)
      ·
        refine ⟨355173397594196766179719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 473564530125595688239625 355173397594196766179719)
        ·
          refine ⟨532760096391295149269579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 355173397594196766179719 532760096391295149269579)
          ·
            refine ⟨799140144586942723904369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 532760096391295149269579 799140144586942723904369)
            ·
              refine ⟨599355108440207042928277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 799140144586942723904369 599355108440207042928277)
              ·
                refine ⟨28094770708134705137263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 599355108440207042928277 28094770708134705137263)
                ·
                  rfl

theorem cell21_369322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 6].length) (baseStart_369322 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_369322 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_369322 prefixEnd_369322 := by exact prefixLift 369322
  have htrace : WordTrace (prefixWord ++ tailWord_369322) baseStart_369322 baseEnd_369322 := by
    simpa [prefixWord, tailWord_369322, baseEnd_369322] using wordTrace_append hprefix tailTrace_369322
  have hstable : (prefixWord ++ tailWord_369322).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369322).length < 2 ^ (prefixWord ++ tailWord_369322).sum := by decide
  have hdescent : baseEnd_369322 < baseStart_369322 := by decide
  rcases family_descends (prefixWord ++ tailWord_369322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369364 : List Nat := [2, 4, 1, 3, 2, 9]
def baseStart_369364 : Nat := 118140960795 + 369364 * 2 ^ 59
def prefixEnd_369364 : Nat := 4983230072969 + 3 ^ 40 * 369364 * 2
def baseEnd_369364 : Nat := 3121996188763754655989

theorem tailTrace_369364 : CollatzResearch.WordTrace tailWord_369364 prefixEnd_369364 3121996188763754655989 := by
  unfold tailWord_369364
  simp only [CollatzResearch.WordTrace]
  refine ⟨6735905916932392597033573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8981207889243190129378097 6735905916932392597033573)
  ·
    refine ⟨1262982359424823611943795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6735905916932392597033573 1262982359424823611943795)
    ·
      refine ⟨1894473539137235417915693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1262982359424823611943795 1894473539137235417915693)
      ·
        refine ⟨710427577176463281718385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1894473539137235417915693 710427577176463281718385)
        ·
          refine ⟨532820682882347461288789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 710427577176463281718385 532820682882347461288789)
          ·
            refine ⟨3121996188763754655989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 532820682882347461288789 3121996188763754655989)
            ·
              rfl

theorem cell21_369364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 9].length) (baseStart_369364 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_369364 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_369364 prefixEnd_369364 := by exact prefixLift 369364
  have htrace : WordTrace (prefixWord ++ tailWord_369364) baseStart_369364 baseEnd_369364 := by
    simpa [prefixWord, tailWord_369364, baseEnd_369364] using wordTrace_append hprefix tailTrace_369364
  have hstable : (prefixWord ++ tailWord_369364).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369364).length < 2 ^ (prefixWord ++ tailWord_369364).sum := by decide
  have hdescent : baseEnd_369364 < baseStart_369364 := by decide
  rcases family_descends (prefixWord ++ tailWord_369364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369412 : List Nat := [2, 3, 2, 2, 1, 1, 4, 3, 3]
def baseStart_369412 : Nat := 118140960795 + 369412 * 2 ^ 59
def prefixEnd_369412 : Nat := 4983230072969 + 3 ^ 40 * 369412 * 2
def baseEnd_369412 : Nat := 84304851350583958911605

theorem tailTrace_369412 : CollatzResearch.WordTrace tailWord_369412 prefixEnd_369412 84304851350583958911605 := by
  unfold tailWord_369412
  simp only [CollatzResearch.WordTrace]
  refine ⟨6736781268845444695907245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8982375025127259594542993 6736781268845444695907245)
  ·
    refine ⟨2526292975817041760965217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6736781268845444695907245 2526292975817041760965217)
    ·
      refine ⟨1894719731862781320723913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2526292975817041760965217 1894719731862781320723913)
      ·
        refine ⟨1421039798897085990542935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1894719731862781320723913 1421039798897085990542935)
        ·
          refine ⟨2131559698345628985814403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1421039798897085990542935 2131559698345628985814403)
          ·
            refine ⟨3197339547518443478721605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2131559698345628985814403 3197339547518443478721605)
            ·
              refine ⟨599501165159708152260301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3197339547518443478721605 599501165159708152260301)
              ·
                refine ⟨224812936934890557097613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 599501165159708152260301 224812936934890557097613)
                ·
                  refine ⟨84304851350583958911605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 224812936934890557097613 84304851350583958911605)
                  ·
                    rfl

theorem cell21_369412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 3, 3].length) (baseStart_369412 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_369412 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_369412 prefixEnd_369412 := by exact prefixLift 369412
  have htrace : WordTrace (prefixWord ++ tailWord_369412) baseStart_369412 baseEnd_369412 := by
    simpa [prefixWord, tailWord_369412, baseEnd_369412] using wordTrace_append hprefix tailTrace_369412
  have hstable : (prefixWord ++ tailWord_369412).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369412).length < 2 ^ (prefixWord ++ tailWord_369412).sum := by decide
  have hdescent : baseEnd_369412 < baseStart_369412 := by decide
  rcases family_descends (prefixWord ++ tailWord_369412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369713 : List Nat := [1, 2, 2, 3, 1, 2, 4, 2, 4]
def baseStart_369713 : Nat := 118140960795 + 369713 * 2 ^ 59
def prefixEnd_369713 : Nat := 4983230072969 + 3 ^ 40 * 369713 * 2
def baseEnd_369713 : Nat := 84373543651474324394323

theorem tailTrace_369713 : CollatzResearch.WordTrace tailWord_369713 prefixEnd_369713 84373543651474324394323 := by
  unfold tailWord_369713
  simp only [CollatzResearch.WordTrace]
  refine ⟨13484540909600417798521793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8989693939733611865681195 13484540909600417798521793)
  ·
    refine ⟨10113405682200313348891345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13484540909600417798521793 10113405682200313348891345)
    ·
      refine ⟨7585054261650235011668509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10113405682200313348891345 7585054261650235011668509)
      ·
        refine ⟨2844395348118838129375691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7585054261650235011668509 2844395348118838129375691)
        ·
          refine ⟨4266593022178257194063537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2844395348118838129375691 4266593022178257194063537)
          ·
            refine ⟨3199944766633692895547653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4266593022178257194063537 3199944766633692895547653)
            ·
              refine ⟨599989643743817417915185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3199944766633692895547653 599989643743817417915185)
              ·
                refine ⟨449992232807863063436389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 599989643743817417915185 449992232807863063436389)
                ·
                  refine ⟨84373543651474324394323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 449992232807863063436389 84373543651474324394323)
                  ·
                    rfl

theorem cell21_369713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 2, 4].length) (baseStart_369713 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_369713 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_369713 prefixEnd_369713 := by exact prefixLift 369713
  have htrace : WordTrace (prefixWord ++ tailWord_369713) baseStart_369713 baseEnd_369713 := by
    simpa [prefixWord, tailWord_369713, baseEnd_369713] using wordTrace_append hprefix tailTrace_369713
  have hstable : (prefixWord ++ tailWord_369713).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369713).length < 2 ^ (prefixWord ++ tailWord_369713).sum := by decide
  have hdescent : baseEnd_369713 < baseStart_369713 := by decide
  rcases family_descends (prefixWord ++ tailWord_369713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369750 : List Nat := [5, 2, 2, 1, 2, 1, 2, 3, 3]
def baseStart_369750 : Nat := 118140960795 + 369750 * 2 ^ 59
def prefixEnd_369750 : Nat := 4983230072969 + 3 ^ 40 * 369750 * 2
def baseEnd_369750 : Nat := 84381987555570482277581

theorem tailTrace_369750 : CollatzResearch.WordTrace tailWord_369750 prefixEnd_369750 84381987555570482277581 := by
  unfold tailWord_369750
  simp only [CollatzResearch.WordTrace]
  refine ⟨842868150654148319851169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8990593606977582078412469 842868150654148319851169)
  ·
    refine ⟨632151112990611239888377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 842868150654148319851169 632151112990611239888377)
    ·
      refine ⟨474113334742958429916283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 632151112990611239888377 474113334742958429916283)
      ·
        refine ⟨711170002114437644874425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 474113334742958429916283 711170002114437644874425)
        ·
          refine ⟨533377501585828233655819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 711170002114437644874425 533377501585828233655819)
          ·
            refine ⟨800066252378742350483729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 533377501585828233655819 800066252378742350483729)
            ·
              refine ⟨600049689284056762862797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 800066252378742350483729 600049689284056762862797)
              ·
                refine ⟨225018633481521286073549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 600049689284056762862797 225018633481521286073549)
                ·
                  refine ⟨84381987555570482277581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 225018633481521286073549 84381987555570482277581)
                  ·
                    rfl

theorem cell21_369750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_369750 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_369750 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_369750 prefixEnd_369750 := by exact prefixLift 369750
  have htrace : WordTrace (prefixWord ++ tailWord_369750) baseStart_369750 baseEnd_369750 := by
    simpa [prefixWord, tailWord_369750, baseEnd_369750] using wordTrace_append hprefix tailTrace_369750
  have hstable : (prefixWord ++ tailWord_369750).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369750).length < 2 ^ (prefixWord ++ tailWord_369750).sum := by decide
  have hdescent : baseEnd_369750 < baseStart_369750 := by decide
  rcases family_descends (prefixWord ++ tailWord_369750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369772 : List Nat := [2, 2, 1, 1, 3, 2, 3, 1, 6]
def baseStart_369772 : Nat := 118140960795 + 369772 * 2 ^ 59
def prefixEnd_369772 : Nat := 4983230072969 + 3 ^ 40 * 369772 * 2
def baseEnd_369772 : Nat := 84387008255303332910869

theorem tailTrace_369772 : CollatzResearch.WordTrace tailWord_369772 prefixEnd_369772 84387008255303332910869 := by
  unfold tailWord_369772
  simp only [CollatzResearch.WordTrace]
  refine ⟨6743346408193335437459785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8991128544257780583279713 6743346408193335437459785)
  ·
    refine ⟨5057509806145001578094839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6743346408193335437459785 5057509806145001578094839)
    ·
      refine ⟨7586264709217502367142259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5057509806145001578094839 7586264709217502367142259)
      ·
        refine ⟨11379397063826253550713389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7586264709217502367142259 11379397063826253550713389)
        ·
          refine ⟨4267273898934845081517521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11379397063826253550713389 4267273898934845081517521)
          ·
            refine ⟨3200455424201133811138141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4267273898934845081517521 3200455424201133811138141)
            ·
              refine ⟨1200170784075425179176803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3200455424201133811138141 1200170784075425179176803)
              ·
                refine ⟨1800256176113137768765205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1200170784075425179176803 1800256176113137768765205)
                ·
                  refine ⟨84387008255303332910869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1800256176113137768765205 84387008255303332910869)
                  ·
                    rfl

theorem cell21_369772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 6].length) (baseStart_369772 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_369772 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_369772 prefixEnd_369772 := by exact prefixLift 369772
  have htrace : WordTrace (prefixWord ++ tailWord_369772) baseStart_369772 baseEnd_369772 := by
    simpa [prefixWord, tailWord_369772, baseEnd_369772] using wordTrace_append hprefix tailTrace_369772
  have hstable : (prefixWord ++ tailWord_369772).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369772).length < 2 ^ (prefixWord ++ tailWord_369772).sum := by decide
  have hdescent : baseEnd_369772 < baseStart_369772 := by decide
  rcases family_descends (prefixWord ++ tailWord_369772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370000 : List Nat := [2, 1, 1, 1, 1, 5, 2, 4, 4]
def baseStart_370000 : Nat := 118140960795 + 370000 * 2 ^ 59
def prefixEnd_370000 : Nat := 4983230072969 + 3 ^ 40 * 370000 * 2
def baseEnd_370000 : Nat := 84439040961625603110403

theorem tailTrace_370000 : CollatzResearch.WordTrace tailWord_370000 prefixEnd_370000 84439040961625603110403 := by
  unfold tailWord_370000
  simp only [CollatzResearch.WordTrace]
  refine ⟨6747504329780332907109727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8996672439707110542812969 6747504329780332907109727)
  ·
    refine ⟨10121256494670499360664591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6747504329780332907109727 10121256494670499360664591)
    ·
      refine ⟨15181884742005749040996887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10121256494670499360664591 15181884742005749040996887)
      ·
        refine ⟨22772827113008623561495331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15181884742005749040996887 22772827113008623561495331)
        ·
          refine ⟨34159240669512935342242997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22772827113008623561495331 34159240669512935342242997)
          ·
            refine ⟨3202428812766837688335281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34159240669512935342242997 3202428812766837688335281)
            ·
              refine ⟨2401821609575128266251461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3202428812766837688335281 2401821609575128266251461)
              ·
                refine ⟨450341551795336549922149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2401821609575128266251461 450341551795336549922149)
                ·
                  refine ⟨84439040961625603110403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 450341551795336549922149 84439040961625603110403)
                  ·
                    rfl

theorem cell21_370000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 4, 4].length) (baseStart_370000 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_370000 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_370000 prefixEnd_370000 := by exact prefixLift 370000
  have htrace : WordTrace (prefixWord ++ tailWord_370000) baseStart_370000 baseEnd_370000 := by
    simpa [prefixWord, tailWord_370000, baseEnd_370000] using wordTrace_append hprefix tailTrace_370000
  have hstable : (prefixWord ++ tailWord_370000).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370000).length < 2 ^ (prefixWord ++ tailWord_370000).sum := by decide
  have hdescent : baseEnd_370000 < baseStart_370000 := by decide
  rcases family_descends (prefixWord ++ tailWord_370000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370003 : List Nat := [1, 1, 1, 2, 1, 1, 9, 2, 3]
def baseStart_370003 : Nat := 118140960795 + 370003 * 2 ^ 59
def prefixEnd_370003 : Nat := 4983230072969 + 3 ^ 40 * 370003 * 2
def baseEnd_370003 : Nat := 84439725602498264560397

theorem tailTrace_370003 : CollatzResearch.WordTrace tailWord_370003 prefixEnd_370003 84439725602498264560397 := by
  unfold tailWord_370003
  simp only [CollatzResearch.WordTrace]
  refine ⟨13495118078549797326578663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8996745385699864884385775 13495118078549797326578663)
  ·
    refine ⟨20242677117824695989867995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13495118078549797326578663 20242677117824695989867995)
    ·
      refine ⟨30364015676737043984801993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20242677117824695989867995 30364015676737043984801993)
      ·
        refine ⟨22773011757552782988601495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30364015676737043984801993 22773011757552782988601495)
        ·
          refine ⟨34159517636329174482902243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22773011757552782988601495 34159517636329174482902243)
          ·
            refine ⟨51239276454493761724353365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34159517636329174482902243 51239276454493761724353365)
            ·
              refine ⟨300230135475549385103633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 51239276454493761724353365 300230135475549385103633)
              ·
                refine ⟨225172601606662038827725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 300230135475549385103633 225172601606662038827725)
                ·
                  refine ⟨84439725602498264560397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 225172601606662038827725 84439725602498264560397)
                  ·
                    rfl

theorem cell21_370003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9, 2, 3].length) (baseStart_370003 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_370003 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_370003 prefixEnd_370003 := by exact prefixLift 370003
  have htrace : WordTrace (prefixWord ++ tailWord_370003) baseStart_370003 baseEnd_370003 := by
    simpa [prefixWord, tailWord_370003, baseEnd_370003] using wordTrace_append hprefix tailTrace_370003
  have hstable : (prefixWord ++ tailWord_370003).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370003).length < 2 ^ (prefixWord ++ tailWord_370003).sum := by decide
  have hdescent : baseEnd_370003 < baseStart_370003 := by decide
  rcases family_descends (prefixWord ++ tailWord_370003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370183 : List Nat := [1, 1, 4, 3, 2, 2, 2, 6]
def baseStart_370183 : Nat := 118140960795 + 370183 * 2 ^ 59
def prefixEnd_370183 : Nat := 4983230072969 + 3 ^ 40 * 370183 * 2
def baseEnd_370183 : Nat := 28160268018285983853343

theorem tailTrace_370183 : CollatzResearch.WordTrace tailWord_370183 prefixEnd_370183 28160268018285983853343 := by
  unfold tailWord_370183
  simp only [CollatzResearch.WordTrace]
  refine ⟨13501683217897688068131203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9001122145265125378754135 13501683217897688068131203)
  ·
    refine ⟨20252524826846532102196805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13501683217897688068131203 20252524826846532102196805)
    ·
      refine ⟨3797348405033724769161901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20252524826846532102196805 3797348405033724769161901)
      ·
        refine ⟨1424005651887646788435713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3797348405033724769161901 1424005651887646788435713)
        ·
          refine ⟨1068004238915735091326785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1424005651887646788435713 1068004238915735091326785)
          ·
            refine ⟨801003179186801318495089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1068004238915735091326785 801003179186801318495089)
            ·
              refine ⟨600752384390100988871317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 801003179186801318495089 600752384390100988871317)
              ·
                refine ⟨28160268018285983853343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 600752384390100988871317 28160268018285983853343)
                ·
                  rfl

theorem cell21_370183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 6].length) (baseStart_370183 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_370183 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_370183 prefixEnd_370183 := by exact prefixLift 370183
  have htrace : WordTrace (prefixWord ++ tailWord_370183) baseStart_370183 baseEnd_370183 := by
    simpa [prefixWord, tailWord_370183, baseEnd_370183] using wordTrace_append hprefix tailTrace_370183
  have hstable : (prefixWord ++ tailWord_370183).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370183).length < 2 ^ (prefixWord ++ tailWord_370183).sum := by decide
  have hdescent : baseEnd_370183 < baseStart_370183 := by decide
  rcases family_descends (prefixWord ++ tailWord_370183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370186 : List Nat := [3, 1, 2, 2, 2, 4, 2, 1, 4]
def baseStart_370186 : Nat := 118140960795 + 370186 * 2 ^ 59
def prefixEnd_370186 : Nat := 4983230072969 + 3 ^ 40 * 370186 * 2
def baseEnd_370186 : Nat := 84481488695730613010023

theorem tailTrace_370186 : CollatzResearch.WordTrace tailWord_370186 prefixEnd_370186 84481488695730613010023 := by
  unfold tailWord_370186
  simp only [CollatzResearch.WordTrace]
  refine ⟨3375448159221704895122603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9001195091257879720326941 3375448159221704895122603)
  ·
    refine ⟨5063172238832557342683905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3375448159221704895122603 5063172238832557342683905)
    ·
      refine ⟨3797379179124418007012929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5063172238832557342683905 3797379179124418007012929)
      ·
        refine ⟨2848034384343313505259697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3797379179124418007012929 2848034384343313505259697)
        ·
          refine ⟨2136025788257485128944773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2848034384343313505259697 2136025788257485128944773)
          ·
            refine ⟨400504835298278461677145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2136025788257485128944773 400504835298278461677145)
            ·
              refine ⟨300378626473708846257859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 400504835298278461677145 300378626473708846257859)
              ·
                refine ⟨450567939710563269386789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 300378626473708846257859 450567939710563269386789)
                ·
                  refine ⟨84481488695730613010023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 450567939710563269386789 84481488695730613010023)
                  ·
                    rfl

theorem cell21_370186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2, 1, 4].length) (baseStart_370186 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_370186 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_370186 prefixEnd_370186 := by exact prefixLift 370186
  have htrace : WordTrace (prefixWord ++ tailWord_370186) baseStart_370186 baseEnd_370186 := by
    simpa [prefixWord, tailWord_370186, baseEnd_370186] using wordTrace_append hprefix tailTrace_370186
  have hstable : (prefixWord ++ tailWord_370186).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370186).length < 2 ^ (prefixWord ++ tailWord_370186).sum := by decide
  have hdescent : baseEnd_370186 < baseStart_370186 := by decide
  rcases family_descends (prefixWord ++ tailWord_370186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370231 : List Nat := [1, 1, 3, 1, 2, 4, 4, 2, 3]
def baseStart_370231 : Nat := 118140960795 + 370231 * 2 ^ 59
def prefixEnd_370231 : Nat := 4983230072969 + 3 ^ 40 * 370231 * 2
def baseEnd_370231 : Nat := 84491758308820534759931

theorem tailTrace_370231 : CollatzResearch.WordTrace tailWord_370231 prefixEnd_370231 84491758308820534759931 := by
  unfold tailWord_370231
  simp only [CollatzResearch.WordTrace]
  refine ⟨13503433921723792265878547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9002289281149194843919031 13503433921723792265878547)
  ·
    refine ⟨20255150882585688398817821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13503433921723792265878547 20255150882585688398817821)
    ·
      refine ⟨7595681580969633149556683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20255150882585688398817821 7595681580969633149556683)
      ·
        refine ⟨11393522371454449724335025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7595681580969633149556683 11393522371454449724335025)
        ·
          refine ⟨8545141778590837293251269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11393522371454449724335025 8545141778590837293251269)
          ·
            refine ⟨1602214083485781992484613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8545141778590837293251269 1602214083485781992484613)
            ·
              refine ⟨300415140653584123590865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1602214083485781992484613 300415140653584123590865)
              ·
                refine ⟨225311355490188092693149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 300415140653584123590865 225311355490188092693149)
                ·
                  refine ⟨84491758308820534759931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 225311355490188092693149 84491758308820534759931)
                  ·
                    rfl

theorem cell21_370231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4, 2, 3].length) (baseStart_370231 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_370231 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_370231 prefixEnd_370231 := by exact prefixLift 370231
  have htrace : WordTrace (prefixWord ++ tailWord_370231) baseStart_370231 baseEnd_370231 := by
    simpa [prefixWord, tailWord_370231, baseEnd_370231] using wordTrace_append hprefix tailTrace_370231
  have hstable : (prefixWord ++ tailWord_370231).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370231).length < 2 ^ (prefixWord ++ tailWord_370231).sum := by decide
  have hdescent : baseEnd_370231 < baseStart_370231 := by decide
  rcases family_descends (prefixWord ++ tailWord_370231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370290 : List Nat := [3, 2, 1, 2, 3, 2, 2, 1, 5]
def baseStart_370290 : Nat := 118140960795 + 370290 * 2 ^ 59
def prefixEnd_370290 : Nat := 4983230072969 + 3 ^ 40 * 370290 * 2
def baseEnd_370290 : Nat := 84505222912649543276477

theorem tailTrace_370290 : CollatzResearch.WordTrace tailWord_370290 prefixEnd_370290 84505222912649543276477 := by
  unfold tailWord_370290
  simp only [CollatzResearch.WordTrace]
  refine ⟨3376396457127511335569081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9003723885673363561517549 3376396457127511335569081)
  ·
    refine ⟨2532297342845633501676811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3376396457127511335569081 2532297342845633501676811)
    ·
      refine ⟨3798446014268450252515217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2532297342845633501676811 3798446014268450252515217)
      ·
        refine ⟨2848834510701337689386413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3798446014268450252515217 2848834510701337689386413)
        ·
          refine ⟨1068312941513001633519905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2848834510701337689386413 1068312941513001633519905)
          ·
            refine ⟨801234706134751225139929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1068312941513001633519905 801234706134751225139929)
            ·
              refine ⟨600926029601063418854947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 801234706134751225139929 600926029601063418854947)
              ·
                refine ⟨901389044401595128282421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 600926029601063418854947 901389044401595128282421)
                ·
                  refine ⟨84505222912649543276477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 901389044401595128282421 84505222912649543276477)
                  ·
                    rfl

theorem cell21_370290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_370290 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_370290 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_370290 prefixEnd_370290 := by exact prefixLift 370290
  have htrace : WordTrace (prefixWord ++ tailWord_370290) baseStart_370290 baseEnd_370290 := by
    simpa [prefixWord, tailWord_370290, baseEnd_370290] using wordTrace_append hprefix tailTrace_370290
  have hstable : (prefixWord ++ tailWord_370290).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370290).length < 2 ^ (prefixWord ++ tailWord_370290).sum := by decide
  have hdescent : baseEnd_370290 < baseStart_370290 := by decide
  rcases family_descends (prefixWord ++ tailWord_370290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370442 : List Nat := [3, 1, 2, 2, 1, 3, 1, 5, 3]
def baseStart_370442 : Nat := 118140960795 + 370442 * 2 ^ 59
def prefixEnd_370442 : Nat := 4983230072969 + 3 ^ 40 * 370442 * 2
def baseEnd_370442 : Nat := 84539911383531056742833

theorem tailTrace_370442 : CollatzResearch.WordTrace tailWord_370442 prefixEnd_370442 84539911383531056742833 := by
  unfold tailWord_370442
  simp only [CollatzResearch.WordTrace]
  refine ⟨3377782430989843825452395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9007419815972916867873053 3377782430989843825452395)
  ·
    refine ⟨5066673646484765738178593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3377782430989843825452395 5066673646484765738178593)
    ·
      refine ⟨3800005234863574303633945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5066673646484765738178593 3800005234863574303633945)
      ·
        refine ⟨2850003926147680727725459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3800005234863574303633945 2850003926147680727725459)
        ·
          refine ⟨4275005889221521091588189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2850003926147680727725459 4275005889221521091588189)
          ·
            refine ⟨1603127208458070409345571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4275005889221521091588189 1603127208458070409345571)
            ·
              refine ⟨2404690812687105614018357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1603127208458070409345571 2404690812687105614018357)
              ·
                refine ⟨225439763689416151314221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2404690812687105614018357 225439763689416151314221)
                ·
                  refine ⟨84539911383531056742833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 225439763689416151314221 84539911383531056742833)
                  ·
                    rfl

theorem cell21_370442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 5, 3].length) (baseStart_370442 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_370442 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_370442 prefixEnd_370442 := by exact prefixLift 370442
  have htrace : WordTrace (prefixWord ++ tailWord_370442) baseStart_370442 baseEnd_370442 := by
    simpa [prefixWord, tailWord_370442, baseEnd_370442] using wordTrace_append hprefix tailTrace_370442
  have hstable : (prefixWord ++ tailWord_370442).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370442).length < 2 ^ (prefixWord ++ tailWord_370442).sum := by decide
  have hdescent : baseEnd_370442 < baseStart_370442 := by decide
  rcases family_descends (prefixWord ++ tailWord_370442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370456 : List Nat := [2, 1, 2, 3, 1, 1, 5, 2, 4]
def baseStart_370456 : Nat := 118140960795 + 370456 * 2 ^ 59
def prefixEnd_370456 : Nat := 4983230072969 + 3 ^ 40 * 370456 * 2
def baseEnd_370456 : Nat := 84543106374270143509471

theorem tailTrace_370456 : CollatzResearch.WordTrace tailWord_370456 prefixEnd_370456 84543106374270143509471 := by
  unfold tailWord_370456
  simp only [CollatzResearch.WordTrace]
  refine ⟨6755820172954327846409611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9007760230605770461879481 6755820172954327846409611)
  ·
    refine ⟨10133730259431491769614417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6755820172954327846409611 10133730259431491769614417)
    ·
      refine ⟨7600297694573618827210813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10133730259431491769614417 7600297694573618827210813)
      ·
        refine ⟨2850111635465107060204055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7600297694573618827210813 2850111635465107060204055)
        ·
          refine ⟨4275167453197660590306083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2850111635465107060204055 4275167453197660590306083)
          ·
            refine ⟨6412751179796490885459125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4275167453197660590306083 6412751179796490885459125)
            ·
              refine ⟨601195423105921020511793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6412751179796490885459125 601195423105921020511793)
              ·
                refine ⟨450896567329440765383845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 601195423105921020511793 450896567329440765383845)
                ·
                  refine ⟨84543106374270143509471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 450896567329440765383845 84543106374270143509471)
                  ·
                    rfl

theorem cell21_370456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 2, 4].length) (baseStart_370456 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_370456 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_370456 prefixEnd_370456 := by exact prefixLift 370456
  have htrace : WordTrace (prefixWord ++ tailWord_370456) baseStart_370456 baseEnd_370456 := by
    simpa [prefixWord, tailWord_370456, baseEnd_370456] using wordTrace_append hprefix tailTrace_370456
  have hstable : (prefixWord ++ tailWord_370456).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370456).length < 2 ^ (prefixWord ++ tailWord_370456).sum := by decide
  have hdescent : baseEnd_370456 < baseStart_370456 := by decide
  rcases family_descends (prefixWord ++ tailWord_370456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370594 : List Nat := [3, 3, 1, 2, 3, 1, 1, 2, 5]
def baseStart_370594 : Nat := 118140960795 + 370594 * 2 ^ 59
def prefixEnd_370594 : Nat := 4983230072969 + 3 ^ 40 * 370594 * 2
def baseEnd_370594 : Nat := 84574599854412570209189

theorem tailTrace_370594 : CollatzResearch.WordTrace tailWord_370594 prefixEnd_370594 84574599854412570209189 := by
  unfold tailWord_370594
  simp only [CollatzResearch.WordTrace]
  refine ⟨3379168404852176315335709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9011115746272470174228557 3379168404852176315335709)
  ·
    refine ⟨1267188151819566118250891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3379168404852176315335709 1267188151819566118250891)
    ·
      refine ⟨1900782227729349177376337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1267188151819566118250891 1900782227729349177376337)
      ·
        refine ⟨1425586670797011883032253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1900782227729349177376337 1425586670797011883032253)
        ·
          refine ⟨534595001548879456137095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1425586670797011883032253 534595001548879456137095)
          ·
            refine ⟨801892502323319184205643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 534595001548879456137095 801892502323319184205643)
            ·
              refine ⟨1202838753484978776308465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 801892502323319184205643 1202838753484978776308465)
              ·
                refine ⟨902129065113734082231349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1202838753484978776308465 902129065113734082231349)
                ·
                  refine ⟨84574599854412570209189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 902129065113734082231349 84574599854412570209189)
                  ·
                    rfl

theorem cell21_370594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_370594 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_370594 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_370594 prefixEnd_370594 := by exact prefixLift 370594
  have htrace : WordTrace (prefixWord ++ tailWord_370594) baseStart_370594 baseEnd_370594 := by
    simpa [prefixWord, tailWord_370594, baseEnd_370594] using wordTrace_append hprefix tailTrace_370594
  have hstable : (prefixWord ++ tailWord_370594).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370594).length < 2 ^ (prefixWord ++ tailWord_370594).sum := by decide
  have hdescent : baseEnd_370594 < baseStart_370594 := by decide
  rcases family_descends (prefixWord ++ tailWord_370594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370622 : List Nat := [4, 2, 1, 1, 1, 4, 8]
def baseStart_370622 : Nat := 118140960795 + 370622 * 2 ^ 59
def prefixEnd_370622 : Nat := 4983230072969 + 3 ^ 40 * 370622 * 2
def baseEnd_370622 : Nat := 9397887759543415971385

theorem tailTrace_370622 : CollatzResearch.WordTrace tailWord_370622 prefixEnd_370622 9397887759543415971385 := by
  unfold tailWord_370622
  simp only [CollatzResearch.WordTrace]
  refine ⟨1689711857913408255420265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9011796575538177362241413 1689711857913408255420265)
  ·
    refine ⟨1267283893435056191565199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1689711857913408255420265 1267283893435056191565199)
    ·
      refine ⟨1900925840152584287347799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1267283893435056191565199 1900925840152584287347799)
      ·
        refine ⟨2851388760228876431021699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1900925840152584287347799 2851388760228876431021699)
        ·
          refine ⟨4277083140343314646532549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2851388760228876431021699 4277083140343314646532549)
          ·
            refine ⟨801953088814371496224853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4277083140343314646532549 801953088814371496224853)
            ·
              refine ⟨9397887759543415971385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 801953088814371496224853 9397887759543415971385)
              ·
                rfl

theorem cell21_370622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 8].length) (baseStart_370622 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_370622 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_370622 prefixEnd_370622 := by exact prefixLift 370622
  have htrace : WordTrace (prefixWord ++ tailWord_370622) baseStart_370622 baseEnd_370622 := by
    simpa [prefixWord, tailWord_370622, baseEnd_370622] using wordTrace_append hprefix tailTrace_370622
  have hstable : (prefixWord ++ tailWord_370622).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370622).length < 2 ^ (prefixWord ++ tailWord_370622).sum := by decide
  have hdescent : baseEnd_370622 < baseStart_370622 := by decide
  rcases family_descends (prefixWord ++ tailWord_370622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370642 : List Nat := [3, 2, 2, 3, 2, 1, 3, 1, 4]
def baseStart_370642 : Nat := 118140960795 + 370642 * 2 ^ 59
def prefixEnd_370642 : Nat := 4983230072969 + 3 ^ 40 * 370642 * 2
def baseEnd_370642 : Nat := 84585554108375153409091

theorem tailTrace_370642 : CollatzResearch.WordTrace tailWord_370642 prefixEnd_370642 84585554108375153409091 := by
  unfold tailWord_370642
  simp only [CollatzResearch.WordTrace]
  refine ⟨3379606080808702364772545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9012282882156539639393453 3379606080808702364772545)
  ·
    refine ⟨2534704560606526773579409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3379606080808702364772545 2534704560606526773579409)
    ·
      refine ⟨1901028420454895080184557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2534704560606526773579409 1901028420454895080184557)
      ·
        refine ⟨712885657670585655069209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1901028420454895080184557 712885657670585655069209)
        ·
          refine ⟨534664243252939241301907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 712885657670585655069209 534664243252939241301907)
          ·
            refine ⟨801996364879408861952861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 534664243252939241301907 801996364879408861952861)
            ·
              refine ⟨300748636829778323232323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 801996364879408861952861 300748636829778323232323)
              ·
                refine ⟨451122955244667484848485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 300748636829778323232323 451122955244667484848485)
                ·
                  refine ⟨84585554108375153409091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 451122955244667484848485 84585554108375153409091)
                  ·
                    rfl

theorem cell21_370642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3, 1, 4].length) (baseStart_370642 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_370642 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_370642 prefixEnd_370642 := by exact prefixLift 370642
  have htrace : WordTrace (prefixWord ++ tailWord_370642) baseStart_370642 baseEnd_370642 := by
    simpa [prefixWord, tailWord_370642, baseEnd_370642] using wordTrace_append hprefix tailTrace_370642
  have hstable : (prefixWord ++ tailWord_370642).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370642).length < 2 ^ (prefixWord ++ tailWord_370642).sum := by decide
  have hdescent : baseEnd_370642 < baseStart_370642 := by decide
  rcases family_descends (prefixWord ++ tailWord_370642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370681 : List Nat := [1, 2, 1, 3, 1, 4, 9]
def baseStart_370681 : Nat := 118140960795 + 370681 * 2 ^ 59
def prefixEnd_370681 : Nat := 4983230072969 + 3 ^ 40 * 370681 * 2
def baseEnd_370681 : Nat := 9399383826635528028779

theorem tailTrace_370681 : CollatzResearch.WordTrace tailWord_370681 prefixEnd_370681 9399383826635528028779 := by
  unfold tailWord_370681
  simp only [CollatzResearch.WordTrace]
  refine ⟨13519846770093519119759897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9013231180062346079839931 13519846770093519119759897)
  ·
    refine ⟨10139885077570139339819923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13519846770093519119759897 10139885077570139339819923)
    ·
      refine ⟨15209827616355209009729885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10139885077570139339819923 15209827616355209009729885)
      ·
        refine ⟨5703685356133203378648707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15209827616355209009729885 5703685356133203378648707)
        ·
          refine ⟨8555528034199805067973061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5703685356133203378648707 8555528034199805067973061)
          ·
            refine ⟨1604161506412463450244949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8555528034199805067973061 1604161506412463450244949)
            ·
              refine ⟨9399383826635528028779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1604161506412463450244949 9399383826635528028779)
              ·
                rfl

theorem cell21_370681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 9].length) (baseStart_370681 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_370681 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_370681 prefixEnd_370681 := by exact prefixLift 370681
  have htrace : WordTrace (prefixWord ++ tailWord_370681) baseStart_370681 baseEnd_370681 := by
    simpa [prefixWord, tailWord_370681, baseEnd_370681] using wordTrace_append hprefix tailTrace_370681
  have hstable : (prefixWord ++ tailWord_370681).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370681).length < 2 ^ (prefixWord ++ tailWord_370681).sum := by decide
  have hdescent : baseEnd_370681 < baseStart_370681 := by decide
  rcases family_descends (prefixWord ++ tailWord_370681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370712 : List Nat := [2, 1, 2, 3, 2, 1, 2, 1, 7]
def baseStart_370712 : Nat := 118140960795 + 370712 * 2 ^ 59
def prefixEnd_370712 : Nat := 4983230072969 + 3 ^ 40 * 370712 * 2
def baseEnd_370712 : Nat := 84601529062070587242281

theorem tailTrace_370712 : CollatzResearch.WordTrace tailWord_370712 prefixEnd_370712 84601529062070587242281 := by
  unfold tailWord_370712
  simp only [CollatzResearch.WordTrace]
  refine ⟨6760488716490605707069195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9013984955320807609425593 6760488716490605707069195)
  ·
    refine ⟨10140733074735908560603793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6760488716490605707069195 10140733074735908560603793)
    ·
      refine ⟨7605549806051931420452845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10140733074735908560603793 7605549806051931420452845)
      ·
        refine ⟨2852081177269474282669817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7605549806051931420452845 2852081177269474282669817)
        ·
          refine ⟨2139060882952105712002363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2852081177269474282669817 2139060882952105712002363)
          ·
            refine ⟨3208591324428158568003545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2139060882952105712002363 3208591324428158568003545)
            ·
              refine ⟨2406443493321118926002659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3208591324428158568003545 2406443493321118926002659)
              ·
                refine ⟨3609665239981678389003989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2406443493321118926002659 3609665239981678389003989)
                ·
                  refine ⟨84601529062070587242281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3609665239981678389003989 84601529062070587242281)
                  ·
                    rfl

theorem cell21_370712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 7].length) (baseStart_370712 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_370712 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_370712 prefixEnd_370712 := by exact prefixLift 370712
  have htrace : WordTrace (prefixWord ++ tailWord_370712) baseStart_370712 baseEnd_370712 := by
    simpa [prefixWord, tailWord_370712, baseEnd_370712] using wordTrace_append hprefix tailTrace_370712
  have hstable : (prefixWord ++ tailWord_370712).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370712).length < 2 ^ (prefixWord ++ tailWord_370712).sum := by decide
  have hdescent : baseEnd_370712 < baseStart_370712 := by decide
  rcases family_descends (prefixWord ++ tailWord_370712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370743 : List Nat := [1, 1, 3, 1, 2, 2, 3, 4, 4]
def baseStart_370743 : Nat := 118140960795 + 370743 * 2 ^ 59
def prefixEnd_370743 : Nat := 4983230072969 + 3 ^ 40 * 370743 * 2
def baseEnd_370743 : Nat := 84608603684421422225551

theorem tailTrace_370743 : CollatzResearch.WordTrace tailWord_370743 prefixEnd_370743 84608603684421422225551 := by
  unfold tailWord_370743
  simp only [CollatzResearch.WordTrace]
  refine ⟨13522108095868903708516883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9014738730579269139011255 13522108095868903708516883)
  ·
    refine ⟨20283162143803355562775325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13522108095868903708516883 20283162143803355562775325)
    ·
      refine ⟨7606185803926258336040747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20283162143803355562775325 7606185803926258336040747)
      ·
        refine ⟨11409278705889387504061121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7606185803926258336040747 11409278705889387504061121)
        ·
          refine ⟨8556959029417040628045841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11409278705889387504061121 8556959029417040628045841)
          ·
            refine ⟨6417719272062780471034381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8556959029417040628045841 6417719272062780471034381)
            ·
              refine ⟨2406644727023542676637893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6417719272062780471034381 2406644727023542676637893)
              ·
                refine ⟨451245886316914251869605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2406644727023542676637893 451245886316914251869605)
                ·
                  refine ⟨84608603684421422225551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 451245886316914251869605 84608603684421422225551)
                  ·
                    rfl

theorem cell21_370743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 4, 4].length) (baseStart_370743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_370743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_370743 prefixEnd_370743 := by exact prefixLift 370743
  have htrace : WordTrace (prefixWord ++ tailWord_370743) baseStart_370743 baseEnd_370743 := by
    simpa [prefixWord, tailWord_370743, baseEnd_370743] using wordTrace_append hprefix tailTrace_370743
  have hstable : (prefixWord ++ tailWord_370743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370743).length < 2 ^ (prefixWord ++ tailWord_370743).sum := by decide
  have hdescent : baseEnd_370743 < baseStart_370743 := by decide
  rcases family_descends (prefixWord ++ tailWord_370743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370794 : List Nat := [3, 1, 3, 2, 4, 1, 1, 2, 4]
def baseStart_370794 : Nat := 118140960795 + 370794 * 2 ^ 59
def prefixEnd_370794 : Nat := 4983230072969 + 3 ^ 40 * 370794 * 2
def baseEnd_370794 : Nat := 84620242579256666875447

theorem tailTrace_370794 : CollatzResearch.WordTrace tailWord_370794 prefixEnd_370794 84620242579256666875447 := by
  unfold tailWord_370794
  simp only [CollatzResearch.WordTrace]
  refine ⟨3380992054671034854655859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9015978812456092945748957 3380992054671034854655859)
  ·
    refine ⟨5071488082006552281983789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3380992054671034854655859 5071488082006552281983789)
    ·
      refine ⟨1901808030752457105743921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5071488082006552281983789 1901808030752457105743921)
      ·
        refine ⟨1426356023064342829307941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1901808030752457105743921 1426356023064342829307941)
        ·
          refine ⟨267441754324564280495239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1426356023064342829307941 267441754324564280495239)
          ·
            refine ⟨401162631486846420742859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267441754324564280495239 401162631486846420742859)
            ·
              refine ⟨601743947230269631114289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 401162631486846420742859 601743947230269631114289)
              ·
                refine ⟨451307960422702223335717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 601743947230269631114289 451307960422702223335717)
                ·
                  refine ⟨84620242579256666875447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 451307960422702223335717 84620242579256666875447)
                  ·
                    rfl

theorem cell21_370794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 2, 4].length) (baseStart_370794 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_370794 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_370794 prefixEnd_370794 := by exact prefixLift 370794
  have htrace : WordTrace (prefixWord ++ tailWord_370794) baseStart_370794 baseEnd_370794 := by
    simpa [prefixWord, tailWord_370794, baseEnd_370794] using wordTrace_append hprefix tailTrace_370794
  have hstable : (prefixWord ++ tailWord_370794).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370794).length < 2 ^ (prefixWord ++ tailWord_370794).sum := by decide
  have hdescent : baseEnd_370794 < baseStart_370794 := by decide
  rcases family_descends (prefixWord ++ tailWord_370794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370839 : List Nat := [1, 1, 3, 3, 4, 2, 1, 3, 3]
def baseStart_370839 : Nat := 118140960795 + 370839 * 2 ^ 59
def prefixEnd_370839 : Nat := 4983230072969 + 3 ^ 40 * 370839 * 2
def baseEnd_370839 : Nat := 84630512192346588625355

theorem tailTrace_370839 : CollatzResearch.WordTrace tailWord_370839 prefixEnd_370839 84630512192346588625355 := by
  unfold tailWord_370839
  simp only [CollatzResearch.WordTrace]
  refine ⟨13525609503521112104011571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9017073002347408069341047 13525609503521112104011571)
  ·
    refine ⟨20288414255281668156017357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13525609503521112104011571 20288414255281668156017357)
    ·
      refine ⟨7608155345730625558506509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20288414255281668156017357 7608155345730625558506509)
      ·
        refine ⟨2853058254648984584439941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7608155345730625558506509 2853058254648984584439941)
        ·
          refine ⟨534948422746684609582489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2853058254648984584439941 534948422746684609582489)
          ·
            refine ⟨401211317060013457186867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 534948422746684609582489 401211317060013457186867)
            ·
              refine ⟨601816975590020185780301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 401211317060013457186867 601816975590020185780301)
              ·
                refine ⟨225681365846257569667613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 601816975590020185780301 225681365846257569667613)
                ·
                  refine ⟨84630512192346588625355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 225681365846257569667613 84630512192346588625355)
                  ·
                    rfl

theorem cell21_370839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 3, 3].length) (baseStart_370839 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_370839 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_370839 prefixEnd_370839 := by exact prefixLift 370839
  have htrace : WordTrace (prefixWord ++ tailWord_370839) baseStart_370839 baseEnd_370839 := by
    simpa [prefixWord, tailWord_370839, baseEnd_370839] using wordTrace_append hprefix tailTrace_370839
  have hstable : (prefixWord ++ tailWord_370839).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370839).length < 2 ^ (prefixWord ++ tailWord_370839).sum := by decide
  have hdescent : baseEnd_370839 < baseStart_370839 := by decide
  rcases family_descends (prefixWord ++ tailWord_370839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370850 : List Nat := [3, 3, 1, 3, 1, 1, 9]
def baseStart_370850 : Nat := 118140960795 + 370850 * 2 ^ 59
def prefixEnd_370850 : Nat := 4983230072969 + 3 ^ 40 * 370850 * 2
def baseEnd_370850 : Nat := 9403669171357001549111

theorem tailTrace_370850 : CollatzResearch.WordTrace tailWord_370850 prefixEnd_370850 9403669171357001549111 := by
  unfold tailWord_370850
  simp only [CollatzResearch.WordTrace]
  refine ⟨3381502676620315245665501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9017340470987507321774669 3381502676620315245665501)
  ·
    refine ⟨1268063503732618217124563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3381502676620315245665501 1268063503732618217124563)
    ·
      refine ⟨1902095255598927325686845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1268063503732618217124563 1902095255598927325686845)
      ·
        refine ⟨713285720849597747132567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1902095255598927325686845 713285720849597747132567)
        ·
          refine ⟨1069928581274396620698851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 713285720849597747132567 1069928581274396620698851)
          ·
            refine ⟨1604892871911594931048277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1069928581274396620698851 1604892871911594931048277)
            ·
              refine ⟨9403669171357001549111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1604892871911594931048277 9403669171357001549111)
              ·
                rfl

theorem cell21_370850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 9].length) (baseStart_370850 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_370850 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_370850 prefixEnd_370850 := by exact prefixLift 370850
  have htrace : WordTrace (prefixWord ++ tailWord_370850) baseStart_370850 baseEnd_370850 := by
    simpa [prefixWord, tailWord_370850, baseEnd_370850] using wordTrace_append hprefix tailTrace_370850
  have hstable : (prefixWord ++ tailWord_370850).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370850).length < 2 ^ (prefixWord ++ tailWord_370850).sum := by decide
  have hdescent : baseEnd_370850 < baseStart_370850 := by decide
  rcases family_descends (prefixWord ++ tailWord_370850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370915 : List Nat := [1, 1, 1, 8, 1, 1, 1, 4, 3]
def baseStart_370915 : Nat := 118140960795 + 370915 * 2 ^ 59
def prefixEnd_370915 : Nat := 4983230072969 + 3 ^ 40 * 370915 * 2
def baseEnd_370915 : Nat := 84647856427787345358533

theorem tailTrace_370915 : CollatzResearch.WordTrace tailWord_370915 prefixEnd_370915 84647856427787345358533 := by
  unfold tailWord_370915
  simp only [CollatzResearch.WordTrace]
  refine ⟨13528381451245777083778199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9018920967497184722518799 13528381451245777083778199)
  ·
    refine ⟨20292572176868665625667299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13528381451245777083778199 20292572176868665625667299)
    ·
      refine ⟨30438858265302998438500949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20292572176868665625667299 30438858265302998438500949)
      ·
        refine ⟨356705370296519512951183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 30438858265302998438500949 356705370296519512951183)
        ·
          refine ⟨535058055444779269426775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356705370296519512951183 535058055444779269426775)
          ·
            refine ⟨802587083167168904140163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 535058055444779269426775 802587083167168904140163)
            ·
              refine ⟨1203880624750753356210245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 802587083167168904140163 1203880624750753356210245)
              ·
                refine ⟨225727617140766254289421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1203880624750753356210245 225727617140766254289421)
                ·
                  refine ⟨84647856427787345358533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 225727617140766254289421 84647856427787345358533)
                  ·
                    rfl

theorem cell21_370915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 4, 3].length) (baseStart_370915 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_370915 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_370915 prefixEnd_370915 := by exact prefixLift 370915
  have htrace : WordTrace (prefixWord ++ tailWord_370915) baseStart_370915 baseEnd_370915 := by
    simpa [prefixWord, tailWord_370915, baseEnd_370915] using wordTrace_append hprefix tailTrace_370915
  have hstable : (prefixWord ++ tailWord_370915).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370915).length < 2 ^ (prefixWord ++ tailWord_370915).sum := by decide
  have hdescent : baseEnd_370915 < baseStart_370915 := by decide
  rcases family_descends (prefixWord ++ tailWord_370915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370940 : List Nat := [2, 2, 2, 1, 4, 1, 1, 1, 7]
def baseStart_370940 : Nat := 118140960795 + 370940 * 2 ^ 59
def prefixEnd_370940 : Nat := 4983230072969 + 3 ^ 40 * 370940 * 2
def baseEnd_370940 : Nat := 84653561768392857441815

theorem tailTrace_370940 : CollatzResearch.WordTrace tailWord_370940 prefixEnd_370940 84653561768392857441815 := by
  unfold tailWord_370940
  simp only [CollatzResearch.WordTrace]
  refine ⟨6764646638077603176719137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9019528850770137568958849 6764646638077603176719137)
  ·
    refine ⟨5073484978558202382539353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6764646638077603176719137 5073484978558202382539353)
    ·
      refine ⟨3805113733918651786904515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5073484978558202382539353 3805113733918651786904515)
      ·
        refine ⟨5707670600877977680356773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3805113733918651786904515 5707670600877977680356773)
        ·
          refine ⟨1070188237664620815066895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5707670600877977680356773 1070188237664620815066895)
          ·
            refine ⟨1605282356496931222600343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1070188237664620815066895 1605282356496931222600343)
            ·
              refine ⟨2407923534745396833900515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1605282356496931222600343 2407923534745396833900515)
              ·
                refine ⟨3611885302118095250850773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2407923534745396833900515 3611885302118095250850773)
                ·
                  refine ⟨84653561768392857441815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3611885302118095250850773 84653561768392857441815)
                  ·
                    rfl

theorem cell21_370940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 7].length) (baseStart_370940 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_370940 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_370940 prefixEnd_370940 := by exact prefixLift 370940
  have htrace : WordTrace (prefixWord ++ tailWord_370940) baseStart_370940 baseEnd_370940 := by
    simpa [prefixWord, tailWord_370940, baseEnd_370940] using wordTrace_append hprefix tailTrace_370940
  have hstable : (prefixWord ++ tailWord_370940).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370940).length < 2 ^ (prefixWord ++ tailWord_370940).sum := by decide
  have hdescent : baseEnd_370940 < baseStart_370940 := by decide
  rcases family_descends (prefixWord ++ tailWord_370940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370971 : List Nat := [1, 1, 1, 1, 1, 1, 9, 2, 4]
def baseStart_370971 : Nat := 118140960795 + 370971 * 2 ^ 59
def prefixEnd_370971 : Nat := 4983230072969 + 3 ^ 40 * 370971 * 2
def baseEnd_370971 : Nat := 84660636390743692425085

theorem tailTrace_370971 : CollatzResearch.WordTrace tailWord_370971 prefixEnd_370971 84660636390743692425085 := by
  unfold tailWord_370971
  simp only [CollatzResearch.WordTrace]
  refine ⟨13530423939042898647816767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9020282626028599098544511 13530423939042898647816767)
  ·
    refine ⟨20295635908564347971725151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13530423939042898647816767 20295635908564347971725151)
    ·
      refine ⟨30443453862846521957587727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20295635908564347971725151 30443453862846521957587727)
      ·
        refine ⟨45665180794269782936381591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30443453862846521957587727 45665180794269782936381591)
        ·
          refine ⟨68497771191404674404572387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45665180794269782936381591 68497771191404674404572387)
          ·
            refine ⟨102746656787107011606858581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68497771191404674404572387 102746656787107011606858581)
            ·
              refine ⟨602031192111955146133937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 102746656787107011606858581 602031192111955146133937)
              ·
                refine ⟨451523394083966359600453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 602031192111955146133937 451523394083966359600453)
                ·
                  refine ⟨84660636390743692425085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 451523394083966359600453 84660636390743692425085)
                  ·
                    rfl

theorem cell21_370971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 2, 4].length) (baseStart_370971 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_370971 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_370971 prefixEnd_370971 := by exact prefixLift 370971
  have htrace : WordTrace (prefixWord ++ tailWord_370971) baseStart_370971 baseEnd_370971 := by
    simpa [prefixWord, tailWord_370971, baseEnd_370971] using wordTrace_append hprefix tailTrace_370971
  have hstable : (prefixWord ++ tailWord_370971).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370971).length < 2 ^ (prefixWord ++ tailWord_370971).sum := by decide
  have hdescent : baseEnd_370971 < baseStart_370971 := by decide
  rcases family_descends (prefixWord ++ tailWord_370971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370974 : List Nat := [4, 3, 2, 1, 1, 1, 1, 3, 5]
def baseStart_370974 : Nat := 118140960795 + 370974 * 2 ^ 59
def prefixEnd_370974 : Nat := 4983230072969 + 3 ^ 40 * 370974 * 2
def baseEnd_370974 : Nat := 84661321031616353875079

theorem tailTrace_370974 : CollatzResearch.WordTrace tailWord_370974 prefixEnd_370974 84661321031616353875079 := by
  unfold tailWord_370974
  simp only [CollatzResearch.WordTrace]
  refine ⟨1691316669754003770021997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9020355572021353440117317 1691316669754003770021997)
  ·
    refine ⟨634243751157751413758249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1691316669754003770021997 634243751157751413758249)
    ·
      refine ⟨475682813368313560318687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 634243751157751413758249 475682813368313560318687)
      ·
        refine ⟨713524220052470340478031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 475682813368313560318687 713524220052470340478031)
        ·
          refine ⟨1070286330078705510717047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 713524220052470340478031 1070286330078705510717047)
          ·
            refine ⟨1605429495118058266075571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1070286330078705510717047 1605429495118058266075571)
            ·
              refine ⟨2408144242677087399113357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1605429495118058266075571 2408144242677087399113357)
              ·
                refine ⟨903054091003907774667509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2408144242677087399113357 903054091003907774667509)
                ·
                  refine ⟨84661321031616353875079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 903054091003907774667509 84661321031616353875079)
                  ·
                    rfl

theorem cell21_370974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_370974 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_370974 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_370974 prefixEnd_370974 := by exact prefixLift 370974
  have htrace : WordTrace (prefixWord ++ tailWord_370974) baseStart_370974 baseEnd_370974 := by
    simpa [prefixWord, tailWord_370974, baseEnd_370974] using wordTrace_append hprefix tailTrace_370974
  have hstable : (prefixWord ++ tailWord_370974).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370974).length < 2 ^ (prefixWord ++ tailWord_370974).sum := by decide
  have hdescent : baseEnd_370974 < baseStart_370974 := by decide
  rcases family_descends (prefixWord ++ tailWord_370974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371002 : List Nat := [3, 1, 1, 1, 4, 2, 4, 5]
def baseStart_371002 : Nat := 118140960795 + 371002 * 2 ^ 59
def prefixEnd_371002 : Nat := 4983230072969 + 3 ^ 40 * 371002 * 2
def baseEnd_371002 : Nat := 28222570337698175802785

theorem tailTrace_371002 : CollatzResearch.WordTrace tailWord_371002 prefixEnd_371002 28222570337698175802785 := by
  unfold tailWord_371002
  simp only [CollatzResearch.WordTrace]
  refine ⟨3382888650482647735548815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9021036401287060628130173 3382888650482647735548815)
  ·
    refine ⟨5074332975723971603323223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3382888650482647735548815 5074332975723971603323223)
    ·
      refine ⟨7611499463585957404984835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5074332975723971603323223 7611499463585957404984835)
      ·
        refine ⟨11417249195378936107477253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7611499463585957404984835 11417249195378936107477253)
        ·
          refine ⟨2140734224133550520151985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11417249195378936107477253 2140734224133550520151985)
          ·
            refine ⟨1605550668100162890113989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2140734224133550520151985 1605550668100162890113989)
            ·
              refine ⟨301040750268780541896373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1605550668100162890113989 301040750268780541896373)
              ·
                refine ⟨28222570337698175802785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 301040750268780541896373 28222570337698175802785)
                ·
                  rfl

theorem cell21_371002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4, 5].length) (baseStart_371002 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_371002 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_371002 prefixEnd_371002 := by exact prefixLift 371002
  have htrace : WordTrace (prefixWord ++ tailWord_371002) baseStart_371002 baseEnd_371002 := by
    simpa [prefixWord, tailWord_371002, baseEnd_371002] using wordTrace_append hprefix tailTrace_371002
  have hstable : (prefixWord ++ tailWord_371002).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371002).length < 2 ^ (prefixWord ++ tailWord_371002).sum := by decide
  have hdescent : baseEnd_371002 < baseStart_371002 := by decide
  rcases family_descends (prefixWord ++ tailWord_371002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371140 : List Nat := [2, 3, 3, 2, 2, 1, 1, 1, 6]
def baseStart_371140 : Nat := 118140960795 + 371140 * 2 ^ 59
def prefixEnd_371140 : Nat := 4983230072969 + 3 ^ 40 * 371140 * 2
def baseEnd_371140 : Nat := 84699204493236954108073

theorem tailTrace_371140 : CollatzResearch.WordTrace tailWord_371140 prefixEnd_371140 84699204493236954108073 := by
  unfold tailWord_371140
  simp only [CollatzResearch.WordTrace]
  refine ⟨6768293937715320255359437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9024391916953760340479249 6768293937715320255359437)
  ·
    refine ⟨2538110226643245095759789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6768293937715320255359437 2538110226643245095759789)
    ·
      refine ⟨951791334991216910909921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2538110226643245095759789 951791334991216910909921)
      ·
        refine ⟨713843501243412683182441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 951791334991216910909921 713843501243412683182441)
        ·
          refine ⟨535382625932559512386831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 713843501243412683182441 535382625932559512386831)
          ·
            refine ⟨803073938898839268580247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 535382625932559512386831 803073938898839268580247)
            ·
              refine ⟨1204610908348258902870371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 803073938898839268580247 1204610908348258902870371)
              ·
                refine ⟨1806916362522388354305557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1204610908348258902870371 1806916362522388354305557)
                ·
                  refine ⟨84699204493236954108073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1806916362522388354305557 84699204493236954108073)
                  ·
                    rfl

theorem cell21_371140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_371140 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_371140 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_371140 prefixEnd_371140 := by exact prefixLift 371140
  have htrace : WordTrace (prefixWord ++ tailWord_371140) baseStart_371140 baseEnd_371140 := by
    simpa [prefixWord, tailWord_371140, baseEnd_371140] using wordTrace_append hprefix tailTrace_371140
  have hstable : (prefixWord ++ tailWord_371140).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371140).length < 2 ^ (prefixWord ++ tailWord_371140).sum := by decide
  have hdescent : baseEnd_371140 < baseStart_371140 := by decide
  rcases family_descends (prefixWord ++ tailWord_371140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371171 : List Nat := [1, 1, 1, 6, 3, 2, 2, 5]
def baseStart_371171 : Nat := 118140960795 + 371171 * 2 ^ 59
def prefixEnd_371171 : Nat := 4983230072969 + 3 ^ 40 * 371171 * 2
def baseEnd_371171 : Nat := 28235426371862596363781

theorem tailTrace_371171 : CollatzResearch.WordTrace tailWord_371171 prefixEnd_371171 28235426371862596363781 := by
  unfold tailWord_371171
  simp only [CollatzResearch.WordTrace]
  refine ⟨13537718538318332805097367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9025145692212221870064911 13537718538318332805097367)
  ·
    refine ⟨20306577807477499207646051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13537718538318332805097367 20306577807477499207646051)
    ·
      refine ⟨30459866711216248811469077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20306577807477499207646051 30459866711216248811469077)
      ·
        refine ⟨1427806252088261663037613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 30459866711216248811469077 1427806252088261663037613)
        ·
          refine ⟨535427344533098123639105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1427806252088261663037613 535427344533098123639105)
          ·
            refine ⟨401570508399823592729329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 535427344533098123639105 401570508399823592729329)
            ·
              refine ⟨301177881299867694546997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 401570508399823592729329 301177881299867694546997)
              ·
                refine ⟨28235426371862596363781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 301177881299867694546997 28235426371862596363781)
                ·
                  rfl

theorem cell21_371171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2, 5].length) (baseStart_371171 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_371171 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_371171 prefixEnd_371171 := by exact prefixLift 371171
  have htrace : WordTrace (prefixWord ++ tailWord_371171) baseStart_371171 baseEnd_371171 := by
    simpa [prefixWord, tailWord_371171, baseEnd_371171] using wordTrace_append hprefix tailTrace_371171
  have hstable : (prefixWord ++ tailWord_371171).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371171).length < 2 ^ (prefixWord ++ tailWord_371171).sum := by decide
  have hdescent : baseEnd_371171 < baseStart_371171 := by decide
  rcases family_descends (prefixWord ++ tailWord_371171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371303 : List Nat := [1, 1, 5, 1, 1, 1, 1, 1, 9]
def baseStart_371303 : Nat := 118140960795 + 371303 * 2 ^ 59
def prefixEnd_371303 : Nat := 4983230072969 + 3 ^ 40 * 371303 * 2
def baseEnd_371303 : Nat := 84736403313984892891073

theorem tailTrace_371303 : CollatzResearch.WordTrace tailWord_371303 prefixEnd_371303 84736403313984892891073 := by
  unfold tailWord_371303
  simp only [CollatzResearch.WordTrace]
  refine ⟨13542532973840119348902563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9028355315893412899268375 13542532973840119348902563)
  ·
    refine ⟨20313799460760179023353845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13542532973840119348902563 20313799460760179023353845)
    ·
      refine ⟨1904418699446266783439423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20313799460760179023353845 1904418699446266783439423)
      ·
        refine ⟨2856628049169400175159135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1904418699446266783439423 2856628049169400175159135)
        ·
          refine ⟨4284942073754100262738703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2856628049169400175159135 4284942073754100262738703)
          ·
            refine ⟨6427413110631150394108055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4284942073754100262738703 6427413110631150394108055)
            ·
              refine ⟨9641119665946725591162083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6427413110631150394108055 9641119665946725591162083)
              ·
                refine ⟨14461679498920088386743125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9641119665946725591162083 14461679498920088386743125)
                ·
                  refine ⟨84736403313984892891073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 14461679498920088386743125 84736403313984892891073)
                  ·
                    rfl

theorem cell21_371303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 9].length) (baseStart_371303 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_371303 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_371303 prefixEnd_371303 := by exact prefixLift 371303
  have htrace : WordTrace (prefixWord ++ tailWord_371303) baseStart_371303 baseEnd_371303 := by
    simpa [prefixWord, tailWord_371303, baseEnd_371303] using wordTrace_append hprefix tailTrace_371303
  have hstable : (prefixWord ++ tailWord_371303).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371303).length < 2 ^ (prefixWord ++ tailWord_371303).sum := by decide
  have hdescent : baseEnd_371303 < baseStart_371303 := by decide
  rcases family_descends (prefixWord ++ tailWord_371303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371427 : List Nat := [1, 1, 1, 7, 1, 1, 1, 4, 4]
def baseStart_371427 : Nat := 118140960795 + 371427 * 2 ^ 59
def prefixEnd_371427 : Nat := 4983230072969 + 3 ^ 40 * 371427 * 2
def baseEnd_371427 : Nat := 84764701803388232824153

theorem tailTrace_371427 : CollatzResearch.WordTrace tailWord_371427 prefixEnd_371427 84764701803388232824153 := by
  unfold tailWord_371427
  simp only [CollatzResearch.WordTrace]
  refine ⟨13547055625390888526416535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9031370416927259017611023 13547055625390888526416535)
  ·
    refine ⟨20320583438086332789624803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13547055625390888526416535 20320583438086332789624803)
    ·
      refine ⟨30480875157129499184437205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20320583438086332789624803 30480875157129499184437205)
      ·
        refine ⟨714395511495222637135247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 30480875157129499184437205 714395511495222637135247)
        ·
          refine ⟨1071593267242833955702871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 714395511495222637135247 1071593267242833955702871)
          ·
            refine ⟨1607389900864250933554307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1071593267242833955702871 1607389900864250933554307)
            ·
              refine ⟨2411084851296376400331461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1607389900864250933554307 2411084851296376400331461)
              ·
                refine ⟨452078409618070575062149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2411084851296376400331461 452078409618070575062149)
                ·
                  refine ⟨84764701803388232824153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 452078409618070575062149 84764701803388232824153)
                  ·
                    rfl

theorem cell21_371427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 4, 4].length) (baseStart_371427 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_371427 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_371427 prefixEnd_371427 := by exact prefixLift 371427
  have htrace : WordTrace (prefixWord ++ tailWord_371427) baseStart_371427 baseEnd_371427 := by
    simpa [prefixWord, tailWord_371427, baseEnd_371427] using wordTrace_append hprefix tailTrace_371427
  have hstable : (prefixWord ++ tailWord_371427).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371427).length < 2 ^ (prefixWord ++ tailWord_371427).sum := by decide
  have hdescent : baseEnd_371427 < baseStart_371427 := by decide
  rcases family_descends (prefixWord ++ tailWord_371427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371500 : List Nat := [2, 2, 1, 1, 1, 4, 2, 8]
def baseStart_371500 : Nat := 118140960795 + 371500 * 2 ^ 59
def prefixEnd_371500 : Nat := 4983230072969 + 3 ^ 40 * 371500 * 2
def baseEnd_371500 : Nat := 28260453799318776035779

theorem tailTrace_371500 : CollatzResearch.WordTrace tailWord_371500 prefixEnd_371500 28260453799318776035779 := by
  unfold tailWord_371500
  simp only [CollatzResearch.WordTrace]
  refine ⟨6774859077063210996911977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9033145436084281329215969 6774859077063210996911977)
  ·
    refine ⟨5081144307797408247683983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6774859077063210996911977 5081144307797408247683983)
    ·
      refine ⟨7621716461696112371525975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5081144307797408247683983 7621716461696112371525975)
      ·
        refine ⟨11432574692544168557288963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7621716461696112371525975 11432574692544168557288963)
        ·
          refine ⟨17148862038816252835933445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11432574692544168557288963 17148862038816252835933445)
          ·
            refine ⟨3215411632278047406737521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17148862038816252835933445 3215411632278047406737521)
            ·
              refine ⟨2411558724208535555053141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3215411632278047406737521 2411558724208535555053141)
              ·
                refine ⟨28260453799318776035779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2411558724208535555053141 28260453799318776035779)
                ·
                  rfl

theorem cell21_371500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 8].length) (baseStart_371500 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_371500 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_371500 prefixEnd_371500 := by exact prefixLift 371500
  have htrace : WordTrace (prefixWord ++ tailWord_371500) baseStart_371500 baseEnd_371500 := by
    simpa [prefixWord, tailWord_371500, baseEnd_371500] using wordTrace_append hprefix tailTrace_371500
  have hstable : (prefixWord ++ tailWord_371500).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371500).length < 2 ^ (prefixWord ++ tailWord_371500).sum := by decide
  have hdescent : baseEnd_371500 < baseStart_371500 := by decide
  rcases family_descends (prefixWord ++ tailWord_371500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371554 : List Nat := [3, 3, 2, 1, 4, 1, 2, 1, 4]
def baseStart_371554 : Nat := 118140960795 + 371554 * 2 ^ 59
def prefixEnd_371554 : Nat := 4983230072969 + 3 ^ 40 * 371554 * 2
def baseEnd_371554 : Nat := 84793684933664234207227

theorem tailTrace_371554 : CollatzResearch.WordTrace tailWord_371554 prefixEnd_371554 84793684933664234207227 := by
  unfold tailWord_371554
  simp only [CollatzResearch.WordTrace]
  refine ⟨3387921923982697304072429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9034458463953859477526477 3387921923982697304072429)
  ·
    refine ⟨1270470721493511489027161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3387921923982697304072429 1270470721493511489027161)
    ·
      refine ⟨952853041120133616770371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1270470721493511489027161 952853041120133616770371)
      ·
        refine ⟨1429279561680200425155557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 952853041120133616770371 1429279561680200425155557)
        ·
          refine ⟨267989917815037579716667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1429279561680200425155557 267989917815037579716667)
          ·
            refine ⟨401984876722556369575001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267989917815037579716667 401984876722556369575001)
            ·
              refine ⟨301488657541917277181251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 401984876722556369575001 301488657541917277181251)
              ·
                refine ⟨452232986312875915771877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 301488657541917277181251 452232986312875915771877)
                ·
                  refine ⟨84793684933664234207227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 452232986312875915771877 84793684933664234207227)
                  ·
                    rfl

theorem cell21_371554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_371554 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_371554 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_371554 prefixEnd_371554 := by exact prefixLift 371554
  have htrace : WordTrace (prefixWord ++ tailWord_371554) baseStart_371554 baseEnd_371554 := by
    simpa [prefixWord, tailWord_371554, baseEnd_371554] using wordTrace_append hprefix tailTrace_371554
  have hstable : (prefixWord ++ tailWord_371554).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371554).length < 2 ^ (prefixWord ++ tailWord_371554).sum := by decide
  have hdescent : baseEnd_371554 < baseStart_371554 := by decide
  rcases family_descends (prefixWord ++ tailWord_371554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371607 : List Nat := [1, 1, 3, 3, 1, 2, 2, 3, 5]
def baseStart_371607 : Nat := 118140960795 + 371607 * 2 ^ 59
def prefixEnd_371607 : Nat := 4983230072969 + 3 ^ 40 * 371607 * 2
def baseEnd_371607 : Nat := 84805780255747919823785

theorem tailTrace_371607 : CollatzResearch.WordTrace tailWord_371607 prefixEnd_371607 84805780255747919823785 := by
  unfold tailWord_371607
  simp only [CollatzResearch.WordTrace]
  refine ⟨13553620764738779267969075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9035747176492519511979383 13553620764738779267969075)
  ·
    refine ⟨20330431147108168901953613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13553620764738779267969075 20330431147108168901953613)
    ·
      refine ⟨7623911680165563338232605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20330431147108168901953613 7623911680165563338232605)
      ·
        refine ⟨2858966880062086251837227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7623911680165563338232605 2858966880062086251837227)
        ·
          refine ⟨4288450320093129377755841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2858966880062086251837227 4288450320093129377755841)
          ·
            refine ⟨3216337740069847033316881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4288450320093129377755841 3216337740069847033316881)
            ·
              refine ⟨2412253305052385274987661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3216337740069847033316881 2412253305052385274987661)
              ·
                refine ⟨904594989394644478120373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2412253305052385274987661 904594989394644478120373)
                ·
                  refine ⟨84805780255747919823785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 904594989394644478120373 84805780255747919823785)
                  ·
                    rfl

theorem cell21_371607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3, 5].length) (baseStart_371607 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_371607 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_371607 prefixEnd_371607 := by exact prefixLift 371607
  have htrace : WordTrace (prefixWord ++ tailWord_371607) baseStart_371607 baseEnd_371607 := by
    simpa [prefixWord, tailWord_371607, baseEnd_371607] using wordTrace_append hprefix tailTrace_371607
  have hstable : (prefixWord ++ tailWord_371607).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371607).length < 2 ^ (prefixWord ++ tailWord_371607).sum := by decide
  have hdescent : baseEnd_371607 < baseStart_371607 := by decide
  rcases family_descends (prefixWord ++ tailWord_371607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371610 : List Nat := [3, 1, 1, 4, 3, 2, 1, 6]
def baseStart_371610 : Nat := 118140960795 + 371610 * 2 ^ 59
def prefixEnd_371610 : Nat := 4983230072969 + 3 ^ 40 * 371610 * 2
def baseEnd_371610 : Nat := 28268821632206860424593

theorem tailTrace_371610 : CollatzResearch.WordTrace tailWord_371610 prefixEnd_371610 28268821632206860424593 := by
  unfold tailWord_371610
  simp only [CollatzResearch.WordTrace]
  refine ⟨3388432545931977695082071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9035820122485273853552189 3388432545931977695082071)
  ·
    refine ⟨5082648818897966542623107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3388432545931977695082071 5082648818897966542623107)
    ·
      refine ⟨7623973228346949813934661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5082648818897966542623107 7623973228346949813934661)
      ·
        refine ⟨1429494980315053090112749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7623973228346949813934661 1429494980315053090112749)
        ·
          refine ⟨536060617618144908792281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1429494980315053090112749 536060617618144908792281)
          ·
            refine ⟨402045463213608681594211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 536060617618144908792281 402045463213608681594211)
            ·
              refine ⟨603068194820413022391317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 402045463213608681594211 603068194820413022391317)
              ·
                refine ⟨28268821632206860424593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 603068194820413022391317 28268821632206860424593)
                ·
                  rfl

theorem cell21_371610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 6].length) (baseStart_371610 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_371610 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_371610 prefixEnd_371610 := by exact prefixLift 371610
  have htrace : WordTrace (prefixWord ++ tailWord_371610) baseStart_371610 baseEnd_371610 := by
    simpa [prefixWord, tailWord_371610, baseEnd_371610] using wordTrace_append hprefix tailTrace_371610
  have hstable : (prefixWord ++ tailWord_371610).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371610).length < 2 ^ (prefixWord ++ tailWord_371610).sum := by decide
  have hdescent : baseEnd_371610 < baseStart_371610 := by decide
  rcases family_descends (prefixWord ++ tailWord_371610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371621 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 10]
def baseStart_371621 : Nat := 118140960795 + 371621 * 2 ^ 59
def prefixEnd_371621 : Nat := 4983230072969 + 3 ^ 40 * 371621 * 2
def baseEnd_371621 : Nat := 84808975246487006590423

theorem tailTrace_371621 : CollatzResearch.WordTrace tailWord_371621 prefixEnd_371621 84808975246487006590423 := by
  unfold tailWord_371621
  simp only [CollatzResearch.WordTrace]
  refine ⟨13554131386688059658978717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9036087591125373105985811 13554131386688059658978717)
  ·
    refine ⟨5082799270008022372117019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13554131386688059658978717 5082799270008022372117019)
    ·
      refine ⟨7624198905012033558175529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5082799270008022372117019 7624198905012033558175529)
      ·
        refine ⟨5718149178759025168631647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7624198905012033558175529 5718149178759025168631647)
        ·
          refine ⟨8577223768138537752947471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5718149178759025168631647 8577223768138537752947471)
          ·
            refine ⟨12865835652207806629421207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8577223768138537752947471 12865835652207806629421207)
            ·
              refine ⟨19298753478311709944131811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12865835652207806629421207 19298753478311709944131811)
              ·
                refine ⟨28948130217467564916197717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19298753478311709944131811 28948130217467564916197717)
                ·
                  refine ⟨84808975246487006590423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 28948130217467564916197717 84808975246487006590423)
                  ·
                    rfl

theorem cell21_371621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 10].length) (baseStart_371621 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_371621 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_371621 prefixEnd_371621 := by exact prefixLift 371621
  have htrace : WordTrace (prefixWord ++ tailWord_371621) baseStart_371621 baseEnd_371621 := by
    simpa [prefixWord, tailWord_371621, baseEnd_371621] using wordTrace_append hprefix tailTrace_371621
  have hstable : (prefixWord ++ tailWord_371621).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371621).length < 2 ^ (prefixWord ++ tailWord_371621).sum := by decide
  have hdescent : baseEnd_371621 < baseStart_371621 := by decide
  rcases family_descends (prefixWord ++ tailWord_371621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371641 : List Nat := [1, 2, 1, 4, 2, 3, 2, 3, 3]
def baseStart_371641 : Nat := 118140960795 + 371641 * 2 ^ 59
def prefixEnd_371641 : Nat := 4983230072969 + 3 ^ 40 * 371641 * 2
def baseEnd_371641 : Nat := 84813539518971416257049

theorem tailTrace_371641 : CollatzResearch.WordTrace tailWord_371641 prefixEnd_371641 84813539518971416257049 := by
  unfold tailWord_371641
  simp only [CollatzResearch.WordTrace]
  refine ⟨13554860846615603074706777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9036573897743735383137851 13554860846615603074706777)
  ·
    refine ⟨10166145634961702306030083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13554860846615603074706777 10166145634961702306030083)
    ·
      refine ⟨15249218452442553459045125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10166145634961702306030083 15249218452442553459045125)
      ·
        refine ⟨2859228459832978773570961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15249218452442553459045125 2859228459832978773570961)
        ·
          refine ⟨2144421344874734080178221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2859228459832978773570961 2144421344874734080178221)
          ·
            refine ⟨804158004328025280066833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2144421344874734080178221 804158004328025280066833)
            ·
              refine ⟨603118503246018960050125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 804158004328025280066833 603118503246018960050125)
              ·
                refine ⟨226169438717257110018797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 603118503246018960050125 226169438717257110018797)
                ·
                  refine ⟨84813539518971416257049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 226169438717257110018797 84813539518971416257049)
                  ·
                    rfl

theorem cell21_371641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 3, 3].length) (baseStart_371641 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_371641 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_371641 prefixEnd_371641 := by exact prefixLift 371641
  have htrace : WordTrace (prefixWord ++ tailWord_371641) baseStart_371641 baseEnd_371641 := by
    simpa [prefixWord, tailWord_371641, baseEnd_371641] using wordTrace_append hprefix tailTrace_371641
  have hstable : (prefixWord ++ tailWord_371641).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371641).length < 2 ^ (prefixWord ++ tailWord_371641).sum := by decide
  have hdescent : baseEnd_371641 < baseStart_371641 := by decide
  rcases family_descends (prefixWord ++ tailWord_371641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371683 : List Nat := [1, 1, 1, 6, 1, 1, 1, 4, 5]
def baseStart_371683 : Nat := 118140960795 + 371683 * 2 ^ 59
def prefixEnd_371683 : Nat := 4983230072969 + 3 ^ 40 * 371683 * 2
def baseEnd_371683 : Nat := 84823124491188676556963

theorem tailTrace_371683 : CollatzResearch.WordTrace tailWord_371683 prefixEnd_371683 84823124491188676556963 := by
  unfold tailWord_371683
  simp only [CollatzResearch.WordTrace]
  refine ⟨13556392712463444247735703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9037595141642296165157135 13556392712463444247735703)
  ·
    refine ⟨20334589068695166371603555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13556392712463444247735703 20334589068695166371603555)
    ·
      refine ⟨30501883603042749557405333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20334589068695166371603555 30501883603042749557405333)
      ·
        refine ⟨1429775793892628885503375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 30501883603042749557405333 1429775793892628885503375)
        ·
          refine ⟨2144663690838943328255063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1429775793892628885503375 2144663690838943328255063)
          ·
            refine ⟨3216995536258414992382595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2144663690838943328255063 3216995536258414992382595)
            ·
              refine ⟨4825493304387622488573893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3216995536258414992382595 4825493304387622488573893)
              ·
                refine ⟨904779994572679216607605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4825493304387622488573893 904779994572679216607605)
                ·
                  refine ⟨84823124491188676556963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 904779994572679216607605 84823124491188676556963)
                  ·
                    rfl

theorem cell21_371683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 4, 5].length) (baseStart_371683 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_371683 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_371683 prefixEnd_371683 := by exact prefixLift 371683
  have htrace : WordTrace (prefixWord ++ tailWord_371683) baseStart_371683 baseEnd_371683 := by
    simpa [prefixWord, tailWord_371683, baseEnd_371683] using wordTrace_append hprefix tailTrace_371683
  have hstable : (prefixWord ++ tailWord_371683).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371683).length < 2 ^ (prefixWord ++ tailWord_371683).sum := by decide
  have hdescent : baseEnd_371683 < baseStart_371683 := by decide
  rcases family_descends (prefixWord ++ tailWord_371683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371717 : List Nat := [1, 3, 1, 1, 2, 3, 5, 2, 3]
def baseStart_371717 : Nat := 118140960795 + 371717 * 2 ^ 59
def prefixEnd_371717 : Nat := 4983230072969 + 3 ^ 40 * 371717 * 2
def baseEnd_371717 : Nat := 84830883754412172990227

theorem tailTrace_371717 : CollatzResearch.WordTrace tailWord_371717 prefixEnd_371717 84830883754412172990227 := by
  unfold tailWord_371717
  simp only [CollatzResearch.WordTrace]
  refine ⟨13557632794340268054473405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9038421862893512036315603 13557632794340268054473405)
  ·
    refine ⟨5084112297877600520427527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13557632794340268054473405 5084112297877600520427527)
    ·
      refine ⟨7626168446816400780641291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5084112297877600520427527 7626168446816400780641291)
      ·
        refine ⟨11439252670224601170961937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7626168446816400780641291 11439252670224601170961937)
        ·
          refine ⟨8579439502668450878221453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11439252670224601170961937 8579439502668450878221453)
          ·
            refine ⟨3217289813500669079333045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8579439502668450878221453 3217289813500669079333045)
            ·
              refine ⟨301620920015687726187473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3217289813500669079333045 301620920015687726187473)
              ·
                refine ⟨226215690011765794640605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 301620920015687726187473 226215690011765794640605)
                ·
                  refine ⟨84830883754412172990227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 226215690011765794640605 84830883754412172990227)
                  ·
                    rfl

theorem cell21_371717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5, 2, 3].length) (baseStart_371717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_371717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_371717 prefixEnd_371717 := by exact prefixLift 371717
  have htrace : WordTrace (prefixWord ++ tailWord_371717) baseStart_371717 baseEnd_371717 := by
    simpa [prefixWord, tailWord_371717, baseEnd_371717] using wordTrace_append hprefix tailTrace_371717
  have hstable : (prefixWord ++ tailWord_371717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371717).length < 2 ^ (prefixWord ++ tailWord_371717).sum := by decide
  have hdescent : baseEnd_371717 < baseStart_371717 := by decide
  rcases family_descends (prefixWord ++ tailWord_371717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371776 : List Nat := [2, 1, 1, 2, 2, 3, 3, 4, 3]
def baseStart_371776 : Nat := 118140960795 + 371776 * 2 ^ 59
def prefixEnd_371776 : Nat := 4983230072969 + 3 ^ 40 * 371776 * 2
def baseEnd_371776 : Nat := 84844348358241181506773

theorem tailTrace_371776 : CollatzResearch.WordTrace tailWord_371776 prefixEnd_371776 84844348358241181506773 := by
  unfold tailWord_371776
  simp only [CollatzResearch.WordTrace]
  refine ⟨6779892350563260565435591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9039856467417680753914121 6779892350563260565435591)
  ·
    refine ⟨10169838525844890848153387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6779892350563260565435591 10169838525844890848153387)
    ·
      refine ⟨15254757788767336272230081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10169838525844890848153387 15254757788767336272230081)
      ·
        refine ⟨11441068341575502204172561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15254757788767336272230081 11441068341575502204172561)
        ·
          refine ⟨8580801256181626653129421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11441068341575502204172561 8580801256181626653129421)
          ·
            refine ⟨3217800471068109994923533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8580801256181626653129421 3217800471068109994923533)
            ·
              refine ⟨1206675176650541248096325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3217800471068109994923533 1206675176650541248096325)
              ·
                refine ⟨226251595621976484018061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1206675176650541248096325 226251595621976484018061)
                ·
                  refine ⟨84844348358241181506773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 226251595621976484018061 84844348358241181506773)
                  ·
                    rfl

theorem cell21_371776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 4, 3].length) (baseStart_371776 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_371776 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_371776 prefixEnd_371776 := by exact prefixLift 371776
  have htrace : WordTrace (prefixWord ++ tailWord_371776) baseStart_371776 baseEnd_371776 := by
    simpa [prefixWord, tailWord_371776, baseEnd_371776] using wordTrace_append hprefix tailTrace_371776
  have hstable : (prefixWord ++ tailWord_371776).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371776).length < 2 ^ (prefixWord ++ tailWord_371776).sum := by decide
  have hdescent : baseEnd_371776 < baseStart_371776 := by decide
  rcases family_descends (prefixWord ++ tailWord_371776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371790 : List Nat := [4, 1, 1, 1, 1, 3, 1, 5, 4]
def baseStart_371790 : Nat := 118140960795 + 371790 * 2 ^ 59
def prefixEnd_371790 : Nat := 4983230072969 + 3 ^ 40 * 371790 * 2
def baseEnd_371790 : Nat := 84847543348980268273411

theorem tailTrace_371790 : CollatzResearch.WordTrace tailWord_371790 prefixEnd_371790 84847543348980268273411 := by
  unfold tailWord_371790
  simp only [CollatzResearch.WordTrace]
  refine ⟨1695036915384475190235103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9040196882050534347920549 1695036915384475190235103)
  ·
    refine ⟨2542555373076712785352655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1695036915384475190235103 2542555373076712785352655)
    ·
      refine ⟨3813833059615069178028983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2542555373076712785352655 3813833059615069178028983)
      ·
        refine ⟨5720749589422603767043475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3813833059615069178028983 5720749589422603767043475)
        ·
          refine ⟨8581124384133905650565213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5720749589422603767043475 8581124384133905650565213)
          ·
            refine ⟨3217921644050214618961955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8581124384133905650565213 3217921644050214618961955)
            ·
              refine ⟨4826882466075321928442933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3217921644050214618961955 4826882466075321928442933)
              ·
                refine ⟨452520231194561430791525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4826882466075321928442933 452520231194561430791525)
                ·
                  refine ⟨84847543348980268273411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 452520231194561430791525 84847543348980268273411)
                  ·
                    rfl

theorem cell21_371790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_371790 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_371790 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_371790 prefixEnd_371790 := by exact prefixLift 371790
  have htrace : WordTrace (prefixWord ++ tailWord_371790) baseStart_371790 baseEnd_371790 := by
    simpa [prefixWord, tailWord_371790, baseEnd_371790] using wordTrace_append hprefix tailTrace_371790
  have hstable : (prefixWord ++ tailWord_371790).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371790).length < 2 ^ (prefixWord ++ tailWord_371790).sum := by decide
  have hdescent : baseEnd_371790 < baseStart_371790 := by decide
  rcases family_descends (prefixWord ++ tailWord_371790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371810 : List Nat := [3, 3, 2, 2, 1, 2, 2, 3, 3]
def baseStart_371810 : Nat := 118140960795 + 371810 * 2 ^ 59
def prefixEnd_371810 : Nat := 4983230072969 + 3 ^ 40 * 371810 * 2
def baseEnd_371810 : Nat := 84852107621464677940037

theorem tailTrace_371810 : CollatzResearch.WordTrace tailWord_371810 prefixEnd_371810 84852107621464677940037 := by
  unfold tailWord_371810
  simp only [CollatzResearch.WordTrace]
  refine ⟨3390256195750836234402221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9040683188668896625072589 3390256195750836234402221)
  ·
    refine ⟨1271346073406563587900833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3390256195750836234402221 1271346073406563587900833)
    ·
      refine ⟨953509555054922690925625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1271346073406563587900833 953509555054922690925625)
      ·
        refine ⟨715132166291192018194219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 953509555054922690925625 715132166291192018194219)
        ·
          refine ⟨1072698249436788027291329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 715132166291192018194219 1072698249436788027291329)
          ·
            refine ⟨804523687077591020468497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1072698249436788027291329 804523687077591020468497)
            ·
              refine ⟨603392765308193265351373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 804523687077591020468497 603392765308193265351373)
              ·
                refine ⟨226272286990572474506765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 603392765308193265351373 226272286990572474506765)
                ·
                  refine ⟨84852107621464677940037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 226272286990572474506765 84852107621464677940037)
                  ·
                    rfl

theorem cell21_371810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_371810 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_371810 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_371810 prefixEnd_371810 := by exact prefixLift 371810
  have htrace : WordTrace (prefixWord ++ tailWord_371810) baseStart_371810 baseEnd_371810 := by
    simpa [prefixWord, tailWord_371810, baseEnd_371810] using wordTrace_append hprefix tailTrace_371810
  have hstable : (prefixWord ++ tailWord_371810).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371810).length < 2 ^ (prefixWord ++ tailWord_371810).sum := by decide
  have hdescent : baseEnd_371810 < baseStart_371810 := by decide
  rcases family_descends (prefixWord ++ tailWord_371810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371866 : List Nat := [3, 1, 1, 5, 1, 1, 1, 2, 6]
def baseStart_371866 : Nat := 118140960795 + 371866 * 2 ^ 59
def prefixEnd_371866 : Nat := 4983230072969 + 3 ^ 40 * 371866 * 2
def baseEnd_371866 : Nat := 84864887584421025006589

theorem tailTrace_371866 : CollatzResearch.WordTrace tailWord_371866 prefixEnd_371866 84864887584421025006589 := by
  unfold tailWord_371866
  simp only [CollatzResearch.WordTrace]
  refine ⟨3390766817700116625411863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9042044847200311001098301 3390766817700116625411863)
  ·
    refine ⟨5086150226550174938117795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3390766817700116625411863 5086150226550174938117795)
    ·
      refine ⟨7629225339825262407176693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5086150226550174938117795 7629225339825262407176693)
      ·
        refine ⟨715239875608618350672815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7629225339825262407176693 715239875608618350672815)
        ·
          refine ⟨1072859813412927526009223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 715239875608618350672815 1072859813412927526009223)
          ·
            refine ⟨1609289720119391289013835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1072859813412927526009223 1609289720119391289013835)
            ·
              refine ⟨2413934580179086933520753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1609289720119391289013835 2413934580179086933520753)
              ·
                refine ⟨1810450935134315200140565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2413934580179086933520753 1810450935134315200140565)
                ·
                  refine ⟨84864887584421025006589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1810450935134315200140565 84864887584421025006589)
                  ·
                    rfl

theorem cell21_371866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 6].length) (baseStart_371866 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_371866 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_371866 prefixEnd_371866 := by exact prefixLift 371866
  have htrace : WordTrace (prefixWord ++ tailWord_371866) baseStart_371866 baseEnd_371866 := by
    simpa [prefixWord, tailWord_371866, baseEnd_371866] using wordTrace_append hprefix tailTrace_371866
  have hstable : (prefixWord ++ tailWord_371866).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371866).length < 2 ^ (prefixWord ++ tailWord_371866).sum := by decide
  have hdescent : baseEnd_371866 < baseStart_371866 := by decide
  rcases family_descends (prefixWord ++ tailWord_371866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371900 : List Nat := [2, 2, 2, 3, 2, 3, 2, 1, 4]
def baseStart_371900 : Nat := 118140960795 + 371900 * 2 ^ 59
def prefixEnd_371900 : Nat := 4983230072969 + 3 ^ 40 * 371900 * 2
def baseEnd_371900 : Nat := 84872646847644521439853

theorem tailTrace_371900 : CollatzResearch.WordTrace tailWord_371900 prefixEnd_371900 84872646847644521439853 := by
  unfold tailWord_371900
  simp only [CollatzResearch.WordTrace]
  refine ⟨6782153676338645154192577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9042871568451526872256769 6782153676338645154192577)
  ·
    refine ⟨5086615257253983865644433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6782153676338645154192577 5086615257253983865644433)
    ·
      refine ⟨3814961442940487899233325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5086615257253983865644433 3814961442940487899233325)
      ·
        refine ⟨1430610541102682962212497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3814961442940487899233325 1430610541102682962212497)
        ·
          refine ⟨1072957905827012221659373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1430610541102682962212497 1072957905827012221659373)
          ·
            refine ⟨402359214685129583122265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1072957905827012221659373 402359214685129583122265)
            ·
              refine ⟨301769411013847187341699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 402359214685129583122265 301769411013847187341699)
              ·
                refine ⟨452654116520770781012549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 301769411013847187341699 452654116520770781012549)
                ·
                  refine ⟨84872646847644521439853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 452654116520770781012549 84872646847644521439853)
                  ·
                    rfl

theorem cell21_371900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2, 1, 4].length) (baseStart_371900 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_371900 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_371900 prefixEnd_371900 := by exact prefixLift 371900
  have htrace : WordTrace (prefixWord ++ tailWord_371900) baseStart_371900 baseEnd_371900 := by
    simpa [prefixWord, tailWord_371900, baseEnd_371900] using wordTrace_append hprefix tailTrace_371900
  have hstable : (prefixWord ++ tailWord_371900).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371900).length < 2 ^ (prefixWord ++ tailWord_371900).sum := by decide
  have hdescent : baseEnd_371900 < baseStart_371900 := by decide
  rcases family_descends (prefixWord ++ tailWord_371900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371939 : List Nat := [1, 1, 1, 18]
def baseStart_371939 : Nat := 118140960795 + 371939 * 2 ^ 59
def prefixEnd_371939 : Nat := 4983230072969 + 3 ^ 40 * 371939 * 2
def baseEnd_371939 : Nat := 349306778514358519711

theorem tailTrace_371939 : CollatzResearch.WordTrace tailWord_371939 prefixEnd_371939 349306778514358519711 := by
  unfold tailWord_371939
  simp only [CollatzResearch.WordTrace]
  refine ⟨13565729799535999969054871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9043819866357333312703247 13565729799535999969054871)
  ·
    refine ⟨20348594699303999953582307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13565729799535999969054871 20348594699303999953582307)
    ·
      refine ⟨30522892048955999930373461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20348594699303999953582307 30522892048955999930373461)
      ·
        refine ⟨349306778514358519711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 18 30522892048955999930373461 349306778514358519711)
        ·
          rfl

theorem cell21_371939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 18].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 18].length) (baseStart_371939 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_371939 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_371939 prefixEnd_371939 := by exact prefixLift 371939
  have htrace : WordTrace (prefixWord ++ tailWord_371939) baseStart_371939 baseEnd_371939 := by
    simpa [prefixWord, tailWord_371939, baseEnd_371939] using wordTrace_append hprefix tailTrace_371939
  have hstable : (prefixWord ++ tailWord_371939).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371939).length < 2 ^ (prefixWord ++ tailWord_371939).sum := by decide
  have hdescent : baseEnd_371939 < baseStart_371939 := by decide
  rcases family_descends (prefixWord ++ tailWord_371939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372004 : List Nat := [2, 3, 1, 3, 1, 1, 1, 6, 3]
def baseStart_372004 : Nat := 118140960795 + 372004 * 2 ^ 59
def prefixEnd_372004 : Nat := 4983230072969 + 3 ^ 40 * 372004 * 2
def baseEnd_372004 : Nat := 84896381064563451706307

theorem tailTrace_372004 : CollatzResearch.WordTrace tailWord_372004 prefixEnd_372004 84896381064563451706307 := by
  unfold tailWord_372004
  simp only [CollatzResearch.WordTrace]
  refine ⟨6784050272150258035085533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9045400362867010713447377 6784050272150258035085533)
  ·
    refine ⟨2544018852056346763157075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6784050272150258035085533 2544018852056346763157075)
    ·
      refine ⟨3816028278084520144735613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2544018852056346763157075 3816028278084520144735613)
      ·
        refine ⟨1431010604281695054275855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3816028278084520144735613 1431010604281695054275855)
        ·
          refine ⟨2146515906422542581413783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1431010604281695054275855 2146515906422542581413783)
          ·
            refine ⟨3219773859633813872120675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2146515906422542581413783 3219773859633813872120675)
            ·
              refine ⟨4829660789450720808181013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3219773859633813872120675 4829660789450720808181013)
              ·
                refine ⟨226390349505502537883485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4829660789450720808181013 226390349505502537883485)
                ·
                  refine ⟨84896381064563451706307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 226390349505502537883485 84896381064563451706307)
                  ·
                    rfl

theorem cell21_372004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 6, 3].length) (baseStart_372004 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_372004 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_372004 prefixEnd_372004 := by exact prefixLift 372004
  have htrace : WordTrace (prefixWord ++ tailWord_372004) baseStart_372004 baseEnd_372004 := by
    simpa [prefixWord, tailWord_372004, baseEnd_372004] using wordTrace_append hprefix tailTrace_372004
  have hstable : (prefixWord ++ tailWord_372004).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372004).length < 2 ^ (prefixWord ++ tailWord_372004).sum := by decide
  have hdescent : baseEnd_372004 < baseStart_372004 := by decide
  rcases family_descends (prefixWord ++ tailWord_372004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372015 : List Nat := [1, 1, 2, 1, 2, 1, 3, 10]
def baseStart_372015 : Nat := 118140960795 + 372015 * 2 ^ 59
def prefixEnd_372015 : Nat := 4983230072969 + 3 ^ 40 * 372015 * 2
def baseEnd_372015 : Nat := 28299630471476625674317

theorem tailTrace_372015 : CollatzResearch.WordTrace tailWord_372015 prefixEnd_372015 28299630471476625674317 := by
  unfold tailWord_372015
  simp only [CollatzResearch.WordTrace]
  refine ⟨13568501747260664948821499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9045667831507109965880999 13568501747260664948821499)
  ·
    refine ⟨20352752620890997423232249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13568501747260664948821499 20352752620890997423232249)
    ·
      refine ⟨15264564465668248067424187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20352752620890997423232249 15264564465668248067424187)
      ·
        refine ⟨22896846698502372101136281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15264564465668248067424187 22896846698502372101136281)
        ·
          refine ⟨17172635023876779075852211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22896846698502372101136281 17172635023876779075852211)
          ·
            refine ⟨25758952535815168613778317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17172635023876779075852211 25758952535815168613778317)
            ·
              refine ⟨9659607200930688230166869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25758952535815168613778317 9659607200930688230166869)
              ·
                refine ⟨28299630471476625674317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 9659607200930688230166869 28299630471476625674317)
                ·
                  rfl

theorem cell21_372015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 10].length) (baseStart_372015 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_372015 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_372015 prefixEnd_372015 := by exact prefixLift 372015
  have htrace : WordTrace (prefixWord ++ tailWord_372015) baseStart_372015 baseEnd_372015 := by
    simpa [prefixWord, tailWord_372015, baseEnd_372015] using wordTrace_append hprefix tailTrace_372015
  have hstable : (prefixWord ++ tailWord_372015).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372015).length < 2 ^ (prefixWord ++ tailWord_372015).sum := by decide
  have hdescent : baseEnd_372015 < baseStart_372015 := by decide
  rcases family_descends (prefixWord ++ tailWord_372015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372091 : List Nat := [1, 1, 1, 1, 1, 6, 1, 9]
def baseStart_372091 : Nat := 118140960795 + 372091 * 2 ^ 59
def prefixEnd_372091 : Nat := 4983230072969 + 3 ^ 40 * 372091 * 2
def baseEnd_372091 : Nat := 28305411883290211252043

theorem tailTrace_372091 : CollatzResearch.WordTrace tailWord_372091 prefixEnd_372091 28305411883290211252043 := by
  unfold tailWord_372091
  simp only [CollatzResearch.WordTrace]
  refine ⟨13571273694985329928588127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9047515796656886619058751 13571273694985329928588127)
  ·
    refine ⟨20356910542477994892882191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13571273694985329928588127 20356910542477994892882191)
    ·
      refine ⟨30535365813716992339323287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20356910542477994892882191 30535365813716992339323287)
      ·
        refine ⟨45803048720575488508984931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30535365813716992339323287 45803048720575488508984931)
        ·
          refine ⟨68704573080863232763477397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45803048720575488508984931 68704573080863232763477397)
          ·
            refine ⟨3220526863165464035788003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 68704573080863232763477397 3220526863165464035788003)
            ·
              refine ⟨4830790294748196053682005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3220526863165464035788003 4830790294748196053682005)
              ·
                refine ⟨28305411883290211252043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4830790294748196053682005 28305411883290211252043)
                ·
                  rfl

theorem cell21_372091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 9].length) (baseStart_372091 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_372091 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_372091 prefixEnd_372091 := by exact prefixLift 372091
  have htrace : WordTrace (prefixWord ++ tailWord_372091) baseStart_372091 baseEnd_372091 := by
    simpa [prefixWord, tailWord_372091, baseEnd_372091] using wordTrace_append hprefix tailTrace_372091
  have hstable : (prefixWord ++ tailWord_372091).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372091).length < 2 ^ (prefixWord ++ tailWord_372091).sum := by decide
  have hdescent : baseEnd_372091 < baseStart_372091 := by decide
  rcases family_descends (prefixWord ++ tailWord_372091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372114 : List Nat := [3, 2, 3, 3, 1, 1, 1, 4, 3]
def baseStart_372114 : Nat := 118140960795 + 372114 * 2 ^ 59
def prefixEnd_372114 : Nat := 4983230072969 + 3 ^ 40 * 372114 * 2
def baseEnd_372114 : Nat := 84921484563227704872749

theorem tailTrace_372114 : CollatzResearch.WordTrace tailWord_372114 prefixEnd_372114 84921484563227704872749 := by
  unfold tailWord_372114
  simp only [CollatzResearch.WordTrace]
  refine ⟨3393028143475501214168849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9048075049268003237783597 3393028143475501214168849)
  ·
    refine ⟨2544771107606625910626637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3393028143475501214168849 2544771107606625910626637)
    ·
      refine ⟨954289165352484716484989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2544771107606625910626637 954289165352484716484989)
      ·
        refine ⟨357858437007181768681871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 954289165352484716484989 357858437007181768681871)
        ·
          refine ⟨536787655510772653022807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357858437007181768681871 536787655510772653022807)
          ·
            refine ⟨805181483266158979534211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 536787655510772653022807 805181483266158979534211)
            ·
              refine ⟨1207772224899238469301317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 805181483266158979534211 1207772224899238469301317)
              ·
                refine ⟨226457292168607212993997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1207772224899238469301317 226457292168607212993997)
                ·
                  refine ⟨84921484563227704872749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 226457292168607212993997 84921484563227704872749)
                  ·
                    rfl

theorem cell21_372114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 4, 3].length) (baseStart_372114 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_372114 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_372114 prefixEnd_372114 := by exact prefixLift 372114
  have htrace : WordTrace (prefixWord ++ tailWord_372114) baseStart_372114 baseEnd_372114 := by
    simpa [prefixWord, tailWord_372114, baseEnd_372114] using wordTrace_append hprefix tailTrace_372114
  have hstable : (prefixWord ++ tailWord_372114).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372114).length < 2 ^ (prefixWord ++ tailWord_372114).sum := by decide
  have hdescent : baseEnd_372114 < baseStart_372114 := by decide
  rcases family_descends (prefixWord ++ tailWord_372114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372125 : List Nat := [1, 4, 2, 1, 3, 3, 1, 6]
def baseStart_372125 : Nat := 118140960795 + 372125 * 2 ^ 59
def prefixEnd_372125 : Nat := 4983230072969 + 3 ^ 40 * 372125 * 2
def baseEnd_372125 : Nat := 28307998304364710063131

theorem tailTrace_372125 : CollatzResearch.WordTrace tailWord_372125 prefixEnd_372125 28307998304364710063131 := by
  unfold tailWord_372125
  simp only [CollatzResearch.WordTrace]
  refine ⟨13572513776862153735325829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9048342517908102490217219 13572513776862153735325829)
  ·
    refine ⟨2544846333161653825373593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13572513776862153735325829 2544846333161653825373593)
    ·
      refine ⟨1908634749871240369030195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2544846333161653825373593 1908634749871240369030195)
      ·
        refine ⟨2862952124806860553545293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1908634749871240369030195 2862952124806860553545293)
        ·
          refine ⟨1073607046802572707579485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2862952124806860553545293 1073607046802572707579485)
          ·
            refine ⟨402602642550964765342307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1073607046802572707579485 402602642550964765342307)
            ·
              refine ⟨603903963826447148013461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 402602642550964765342307 603903963826447148013461)
              ·
                refine ⟨28307998304364710063131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 603903963826447148013461 28307998304364710063131)
                ·
                  rfl

theorem cell21_372125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 6].length) (baseStart_372125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_372125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_372125 prefixEnd_372125 := by exact prefixLift 372125
  have htrace : WordTrace (prefixWord ++ tailWord_372125) baseStart_372125 baseEnd_372125 := by
    simpa [prefixWord, tailWord_372125, baseEnd_372125] using wordTrace_append hprefix tailTrace_372125
  have hstable : (prefixWord ++ tailWord_372125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372125).length < 2 ^ (prefixWord ++ tailWord_372125).sum := by decide
  have hdescent : baseEnd_372125 < baseStart_372125 := by decide
  rcases family_descends (prefixWord ++ tailWord_372125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372167 : List Nat := [1, 1, 4, 1, 1, 3, 10]
def baseStart_372167 : Nat := 118140960795 + 372167 * 2 ^ 59
def prefixEnd_372167 : Nat := 4983230072969 + 3 ^ 40 * 372167 * 2
def baseEnd_372167 : Nat := 9437064431701265609923

theorem tailTrace_372167 : CollatzResearch.WordTrace tailWord_372167 prefixEnd_372167 9437064431701265609923 := by
  unfold tailWord_372167
  simp only [CollatzResearch.WordTrace]
  refine ⟨13574045642709994908354755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9049363761806663272236503 13574045642709994908354755)
  ·
    refine ⟨20361068464064992362532133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13574045642709994908354755 20361068464064992362532133)
    ·
      refine ⟨3817700337012186067974775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20361068464064992362532133 3817700337012186067974775)
      ·
        refine ⟨5726550505518279101962163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3817700337012186067974775 5726550505518279101962163)
        ·
          refine ⟨8589825758277418652943245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5726550505518279101962163 8589825758277418652943245)
          ·
            refine ⟨3221184659354031994853717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8589825758277418652943245 3221184659354031994853717)
            ·
              refine ⟨9437064431701265609923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3221184659354031994853717 9437064431701265609923)
              ·
                rfl

theorem cell21_372167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 10].length) (baseStart_372167 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_372167 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_372167 prefixEnd_372167 := by exact prefixLift 372167
  have htrace : WordTrace (prefixWord ++ tailWord_372167) baseStart_372167 baseEnd_372167 := by
    simpa [prefixWord, tailWord_372167, baseEnd_372167] using wordTrace_append hprefix tailTrace_372167
  have hstable : (prefixWord ++ tailWord_372167).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372167).length < 2 ^ (prefixWord ++ tailWord_372167).sum := by decide
  have hdescent : baseEnd_372167 < baseStart_372167 := by decide
  rcases family_descends (prefixWord ++ tailWord_372167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372170 : List Nat := [3, 1, 2, 1, 2, 3, 3, 2, 4]
def baseStart_372170 : Nat := 118140960795 + 372170 * 2 ^ 59
def prefixEnd_372170 : Nat := 4983230072969 + 3 ^ 40 * 372170 * 2
def baseEnd_372170 : Nat := 84934264526184051939301

theorem tailTrace_372170 : CollatzResearch.WordTrace tailWord_372170 prefixEnd_372170 84934264526184051939301 := by
  unfold tailWord_372170
  simp only [CollatzResearch.WordTrace]
  refine ⟨3393538765424781605178491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9049436707799417613809309 3393538765424781605178491)
  ·
    refine ⟨5090308148137172407767737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3393538765424781605178491 5090308148137172407767737)
    ·
      refine ⟨3817731111102879305825803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5090308148137172407767737 3817731111102879305825803)
      ·
        refine ⟨5726596666654318958738705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3817731111102879305825803 5726596666654318958738705)
        ·
          refine ⟨4294947499990739219054029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5726596666654318958738705 4294947499990739219054029)
          ·
            refine ⟨1610605312496527207145261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4294947499990739219054029 1610605312496527207145261)
            ·
              refine ⟨603976992186197702679473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1610605312496527207145261 603976992186197702679473)
              ·
                refine ⟨452982744139648277009605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 603976992186197702679473 452982744139648277009605)
                ·
                  refine ⟨84934264526184051939301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 452982744139648277009605 84934264526184051939301)
                  ·
                    rfl

theorem cell21_372170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 2, 4].length) (baseStart_372170 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_372170 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_372170 prefixEnd_372170 := by exact prefixLift 372170
  have htrace : WordTrace (prefixWord ++ tailWord_372170) baseStart_372170 baseEnd_372170 := by
    simpa [prefixWord, tailWord_372170, baseEnd_372170] using wordTrace_append hprefix tailTrace_372170
  have hstable : (prefixWord ++ tailWord_372170).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372170).length < 2 ^ (prefixWord ++ tailWord_372170).sum := by decide
  have hdescent : baseEnd_372170 < baseStart_372170 := by decide
  rcases family_descends (prefixWord ++ tailWord_372170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372215 : List Nat := [1, 1, 3, 1, 1, 1, 1, 9, 3]
def baseStart_372215 : Nat := 118140960795 + 372215 * 2 ^ 59
def prefixEnd_372215 : Nat := 4983230072969 + 3 ^ 40 * 372215 * 2
def baseEnd_372215 : Nat := 84944534139273973689209

theorem tailTrace_372215 : CollatzResearch.WordTrace tailWord_372215 prefixEnd_372215 84944534139273973689209 := by
  unfold tailWord_372215
  simp only [CollatzResearch.WordTrace]
  refine ⟨13575796346536099106102099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9050530897690732737401399 13575796346536099106102099)
  ·
    refine ⟨20363694519804148659153149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13575796346536099106102099 20363694519804148659153149)
    ·
      refine ⟨7636385444926555747182431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20363694519804148659153149 7636385444926555747182431)
      ·
        refine ⟨11454578167389833620773647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7636385444926555747182431 11454578167389833620773647)
        ·
          refine ⟨17181867251084750431160471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11454578167389833620773647 17181867251084750431160471)
          ·
            refine ⟨25772800876627125646740707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17181867251084750431160471 25772800876627125646740707)
            ·
              refine ⟨38659201314940688470111061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25772800876627125646740707 38659201314940688470111061)
              ·
                refine ⟨226518757704730596504557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 38659201314940688470111061 226518757704730596504557)
                ·
                  refine ⟨84944534139273973689209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 226518757704730596504557 84944534139273973689209)
                  ·
                    rfl

theorem cell21_372215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 9, 3].length) (baseStart_372215 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_372215 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_372215 prefixEnd_372215 := by exact prefixLift 372215
  have htrace : WordTrace (prefixWord ++ tailWord_372215) baseStart_372215 baseEnd_372215 := by
    simpa [prefixWord, tailWord_372215, baseEnd_372215] using wordTrace_append hprefix tailTrace_372215
  have hstable : (prefixWord ++ tailWord_372215).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372215).length < 2 ^ (prefixWord ++ tailWord_372215).sum := by decide
  have hdescent : baseEnd_372215 < baseStart_372215 := by decide
  rcases family_descends (prefixWord ++ tailWord_372215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372229 : List Nat := [1, 3, 1, 1, 2, 2, 1, 6, 4]
def baseStart_372229 : Nat := 118140960795 + 372229 * 2 ^ 59
def prefixEnd_372229 : Nat := 4983230072969 + 3 ^ 40 * 372229 * 2
def baseEnd_372229 : Nat := 84947729130013060455847

theorem tailTrace_372229 : CollatzResearch.WordTrace tailWord_372229 prefixEnd_372229 84947729130013060455847 := by
  unfold tailWord_372229
  simp only [CollatzResearch.WordTrace]
  refine ⟨13576306968485379497111741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9050871312323586331407827 13576306968485379497111741)
  ·
    refine ⟨5091115113182017311416903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13576306968485379497111741 5091115113182017311416903)
    ·
      refine ⟨7636672669773025967125355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5091115113182017311416903 7636672669773025967125355)
      ·
        refine ⟨11455009004659538950688033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7636672669773025967125355 11455009004659538950688033)
        ·
          refine ⟨8591256753494654213016025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11455009004659538950688033 8591256753494654213016025)
          ·
            refine ⟨6443442565120990659762019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8591256753494654213016025 6443442565120990659762019)
            ·
              refine ⟨9665163847681485989643029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6443442565120990659762019 9665163847681485989643029)
              ·
                refine ⟨453054555360069655764517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9665163847681485989643029 453054555360069655764517)
                ·
                  refine ⟨84947729130013060455847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 453054555360069655764517 84947729130013060455847)
                  ·
                    rfl

theorem cell21_372229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 6, 4].length) (baseStart_372229 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_372229 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_372229 prefixEnd_372229 := by exact prefixLift 372229
  have htrace : WordTrace (prefixWord ++ tailWord_372229) baseStart_372229 baseEnd_372229 := by
    simpa [prefixWord, tailWord_372229, baseEnd_372229] using wordTrace_append hprefix tailTrace_372229
  have hstable : (prefixWord ++ tailWord_372229).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372229).length < 2 ^ (prefixWord ++ tailWord_372229).sum := by decide
  have hdescent : baseEnd_372229 < baseStart_372229 := by decide
  rcases family_descends (prefixWord ++ tailWord_372229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372243 : List Nat := [1, 1, 1, 2, 1, 6, 1, 8]
def baseStart_372243 : Nat := 118140960795 + 372243 * 2 ^ 59
def prefixEnd_372243 : Nat := 4983230072969 + 3 ^ 40 * 372243 * 2
def baseEnd_372243 : Nat := 28316974706917382407495

theorem tailTrace_372243 : CollatzResearch.WordTrace tailWord_372243 prefixEnd_372243 28316974706917382407495 := by
  unfold tailWord_372243
  simp only [CollatzResearch.WordTrace]
  refine ⟨13576817590434659888121383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9051211726956439925414255 13576817590434659888121383)
  ·
    refine ⟨20365226385651989832182075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13576817590434659888121383 20365226385651989832182075)
    ·
      refine ⟨30547839578477984748273113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20365226385651989832182075 30547839578477984748273113)
      ·
        refine ⟨22910879683858488561204835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30547839578477984748273113 22910879683858488561204835)
        ·
          refine ⟨34366319525787732841807253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22910879683858488561204835 34366319525787732841807253)
          ·
            refine ⟨1610921227771299976959715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 34366319525787732841807253 1610921227771299976959715)
            ·
              refine ⟨2416381841656949965439573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1610921227771299976959715 2416381841656949965439573)
              ·
                refine ⟨28316974706917382407495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2416381841656949965439573 28316974706917382407495)
                ·
                  rfl

theorem cell21_372243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 8].length) (baseStart_372243 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_372243 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_372243 prefixEnd_372243 := by exact prefixLift 372243
  have htrace : WordTrace (prefixWord ++ tailWord_372243) baseStart_372243 baseEnd_372243 := by
    simpa [prefixWord, tailWord_372243, baseEnd_372243] using wordTrace_append hprefix tailTrace_372243
  have hstable : (prefixWord ++ tailWord_372243).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372243).length < 2 ^ (prefixWord ++ tailWord_372243).sum := by decide
  have hdescent : baseEnd_372243 < baseStart_372243 := by decide
  rcases family_descends (prefixWord ++ tailWord_372243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372305 : List Nat := [1, 2, 2, 1, 3, 2, 1, 5, 4]
def baseStart_372305 : Nat := 118140960795 + 372305 * 2 ^ 59
def prefixEnd_372305 : Nat := 4983230072969 + 3 ^ 40 * 372305 * 2
def baseEnd_372305 : Nat := 84965073365453817189025

theorem tailTrace_372305 : CollatzResearch.WordTrace tailWord_372305 prefixEnd_372305 84965073365453817189025 := by
  unfold tailWord_372305
  simp only [CollatzResearch.WordTrace]
  refine ⟨13579078916210044476878369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9052719277473362984585579 13579078916210044476878369)
  ·
    refine ⟨10184309187157533357658777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13579078916210044476878369 10184309187157533357658777)
    ·
      refine ⟨7638231890368150018244083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10184309187157533357658777 7638231890368150018244083)
      ·
        refine ⟨11457347835552225027366125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7638231890368150018244083 11457347835552225027366125)
        ·
          refine ⟨4296505438332084385262297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11457347835552225027366125 4296505438332084385262297)
          ·
            refine ⟨3222379078749063288946723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4296505438332084385262297 3222379078749063288946723)
            ·
              refine ⟨4833568618123594933420085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3222379078749063288946723 4833568618123594933420085)
              ·
                refine ⟨453147057949087025008133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4833568618123594933420085 453147057949087025008133)
                ·
                  refine ⟨84965073365453817189025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 453147057949087025008133 84965073365453817189025)
                  ·
                    rfl

theorem cell21_372305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 5, 4].length) (baseStart_372305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_372305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_372305 prefixEnd_372305 := by exact prefixLift 372305
  have htrace : WordTrace (prefixWord ++ tailWord_372305) baseStart_372305 baseEnd_372305 := by
    simpa [prefixWord, tailWord_372305, baseEnd_372305] using wordTrace_append hprefix tailTrace_372305
  have hstable : (prefixWord ++ tailWord_372305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372305).length < 2 ^ (prefixWord ++ tailWord_372305).sum := by decide
  have hdescent : baseEnd_372305 < baseStart_372305 := by decide
  rcases family_descends (prefixWord ++ tailWord_372305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372370 : List Nat := [3, 2, 3, 1, 3, 2, 2, 5]
def baseStart_372370 : Nat := 118140960795 + 372370 * 2 ^ 59
def prefixEnd_372370 : Nat := 4983230072969 + 3 ^ 40 * 372370 * 2
def baseEnd_372370 : Nat := 28326635750342716201853

theorem tailTrace_372370 : CollatzResearch.WordTrace tailWord_372370 prefixEnd_372370 28326635750342716201853 := by
  unfold tailWord_372370
  simp only [CollatzResearch.WordTrace]
  refine ⟨3395362415243640144498641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9054299773983040385329709 3395362415243640144498641)
  ·
    refine ⟨2546521811432730108373981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3395362415243640144498641 2546521811432730108373981)
    ·
      refine ⟨954945679287273790640243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2546521811432730108373981 954945679287273790640243)
      ·
        refine ⟨1432418518930910685960365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 954945679287273790640243 1432418518930910685960365)
        ·
          refine ⟨537156944599091507235137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1432418518930910685960365 537156944599091507235137)
          ·
            refine ⟨402867708449318630426353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 537156944599091507235137 402867708449318630426353)
            ·
              refine ⟨302150781336988972819765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 402867708449318630426353 302150781336988972819765)
              ·
                refine ⟨28326635750342716201853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 302150781336988972819765 28326635750342716201853)
                ·
                  rfl

theorem cell21_372370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2, 5].length) (baseStart_372370 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_372370 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_372370 prefixEnd_372370 := by exact prefixLift 372370
  have htrace : WordTrace (prefixWord ++ tailWord_372370) baseStart_372370 baseEnd_372370 := by
    simpa [prefixWord, tailWord_372370, baseEnd_372370] using wordTrace_append hprefix tailTrace_372370
  have hstable : (prefixWord ++ tailWord_372370).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372370).length < 2 ^ (prefixWord ++ tailWord_372370).sum := by decide
  have hdescent : baseEnd_372370 < baseStart_372370 := by decide
  rcases family_descends (prefixWord ++ tailWord_372370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372384 : List Nat := [2, 1, 1, 4, 3, 1, 3, 3, 3]
def baseStart_372384 : Nat := 118140960795 + 372384 * 2 ^ 59
def prefixEnd_372384 : Nat := 4983230072969 + 3 ^ 40 * 372384 * 2
def baseEnd_372384 : Nat := 84983102241767235372197

theorem tailTrace_372384 : CollatzResearch.WordTrace tailWord_372384 prefixEnd_372384 84983102241767235372197 := by
  unfold tailWord_372384
  simp only [CollatzResearch.WordTrace]
  refine ⟨6790980141461920484502103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9054640188615893979336137 6790980141461920484502103)
  ·
    refine ⟨10186470212192880726753155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6790980141461920484502103 10186470212192880726753155)
    ·
      refine ⟨15279705318289321090129733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10186470212192880726753155 15279705318289321090129733)
      ·
        refine ⟨2864944747179247704399325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15279705318289321090129733 2864944747179247704399325)
        ·
          refine ⟨1074354280192217889149747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2864944747179247704399325 1074354280192217889149747)
          ·
            refine ⟨1611531420288326833724621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1074354280192217889149747 1611531420288326833724621)
            ·
              refine ⟨604324282608122562646733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1611531420288326833724621 604324282608122562646733)
              ·
                refine ⟨226621605978045960992525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 604324282608122562646733 226621605978045960992525)
                ·
                  refine ⟨84983102241767235372197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 226621605978045960992525 84983102241767235372197)
                  ·
                    rfl

theorem cell21_372384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 3, 3].length) (baseStart_372384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_372384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_372384 prefixEnd_372384 := by exact prefixLift 372384
  have htrace : WordTrace (prefixWord ++ tailWord_372384) baseStart_372384 baseEnd_372384 := by
    simpa [prefixWord, tailWord_372384, baseEnd_372384] using wordTrace_append hprefix tailTrace_372384
  have hstable : (prefixWord ++ tailWord_372384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372384).length < 2 ^ (prefixWord ++ tailWord_372384).sum := by decide
  have hdescent : baseEnd_372384 < baseStart_372384 := by decide
  rcases family_descends (prefixWord ++ tailWord_372384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372412 : List Nat := [2, 2, 2, 3, 1, 3, 2, 6]
def baseStart_372412 : Nat := 118140960795 + 372412 * 2 ^ 59
def prefixEnd_372412 : Nat := 4983230072969 + 3 ^ 40 * 372412 * 2
def baseEnd_372412 : Nat := 28329830741081802968491

theorem tailTrace_372412 : CollatzResearch.WordTrace tailWord_372412 prefixEnd_372412 28329830741081802968491 := by
  unfold tailWord_372412
  simp only [CollatzResearch.WordTrace]
  refine ⟨6791490763411200875511745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9055321017881601167348993 6791490763411200875511745)
  ·
    refine ⟨5093618072558400656633809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6791490763411200875511745 5093618072558400656633809)
    ·
      refine ⟨3820213554418800492475357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5093618072558400656633809 3820213554418800492475357)
      ·
        refine ⟨1432580082907050184678259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3820213554418800492475357 1432580082907050184678259)
        ·
          refine ⟨2148870124360575277017389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1432580082907050184678259 2148870124360575277017389)
          ·
            refine ⟨805826296635215728881521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2148870124360575277017389 805826296635215728881521)
            ·
              refine ⟨604369722476411796661141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 805826296635215728881521 604369722476411796661141)
              ·
                refine ⟨28329830741081802968491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 604369722476411796661141 28329830741081802968491)
                ·
                  rfl

theorem cell21_372412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 6].length) (baseStart_372412 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_372412 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_372412 prefixEnd_372412 := by exact prefixLift 372412
  have htrace : WordTrace (prefixWord ++ tailWord_372412) baseStart_372412 baseEnd_372412 := by
    simpa [prefixWord, tailWord_372412, baseEnd_372412] using wordTrace_append hprefix tailTrace_372412
  have hstable : (prefixWord ++ tailWord_372412).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372412).length < 2 ^ (prefixWord ++ tailWord_372412).sum := by decide
  have hdescent : baseEnd_372412 < baseStart_372412 := by decide
  rcases family_descends (prefixWord ++ tailWord_372412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372429 : List Nat := [1, 6, 2, 1, 1, 1, 2, 7]
def baseStart_372429 : Nat := 118140960795 + 372429 * 2 ^ 59
def prefixEnd_372429 : Nat := 4983230072969 + 3 ^ 40 * 372429 * 2
def baseEnd_372429 : Nat := 28331123951619052374035

theorem tailTrace_372429 : CollatzResearch.WordTrace tailWord_372429 prefixEnd_372429 28331123951619052374035 := by
  unfold tailWord_372429
  simp only [CollatzResearch.WordTrace]
  refine ⟨13583601567760813654392341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9055734378507209102928227 13583601567760813654392341)
  ·
    refine ⟨636731323488788140049641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 13583601567760813654392341 636731323488788140049641)
    ·
      refine ⟨477548492616591105037231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 636731323488788140049641 477548492616591105037231)
      ·
        refine ⟨716322738924886657555847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 477548492616591105037231 716322738924886657555847)
        ·
          refine ⟨1074484108387329986333771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 716322738924886657555847 1074484108387329986333771)
          ·
            refine ⟨1611726162580994979500657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1074484108387329986333771 1611726162580994979500657)
            ·
              refine ⟨1208794621935746234625493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1611726162580994979500657 1208794621935746234625493)
              ·
                refine ⟨28331123951619052374035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1208794621935746234625493 28331123951619052374035)
                ·
                  rfl

theorem cell21_372429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 7].length) (baseStart_372429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_372429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_372429 prefixEnd_372429 := by exact prefixLift 372429
  have htrace : WordTrace (prefixWord ++ tailWord_372429) baseStart_372429 baseEnd_372429 := by
    simpa [prefixWord, tailWord_372429, baseEnd_372429] using wordTrace_append hprefix tailTrace_372429
  have hstable : (prefixWord ++ tailWord_372429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372429).length < 2 ^ (prefixWord ++ tailWord_372429).sum := by decide
  have hdescent : baseEnd_372429 < baseStart_372429 := by decide
  rcases family_descends (prefixWord ++ tailWord_372429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372460 : List Nat := [2, 2, 1, 1, 2, 2, 6, 2, 3]
def baseStart_372460 : Nat := 118140960795 + 372460 * 2 ^ 59
def prefixEnd_372460 : Nat := 4983230072969 + 3 ^ 40 * 372460 * 2
def baseEnd_372460 : Nat := 85000446477207992105375

theorem tailTrace_372460 : CollatzResearch.WordTrace tailWord_372460 prefixEnd_372460 85000446477207992105375 := by
  unfold tailWord_372460
  simp only [CollatzResearch.WordTrace]
  refine ⟨6792366115324252974385417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9056488153765670632513889 6792366115324252974385417)
  ·
    refine ⟨5094274586493189730789063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6792366115324252974385417 5094274586493189730789063)
    ·
      refine ⟨7641411879739784596183595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5094274586493189730789063 7641411879739784596183595)
      ·
        refine ⟨11462117819609676894275393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7641411879739784596183595 11462117819609676894275393)
        ·
          refine ⟨8596588364707257670706545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11462117819609676894275393 8596588364707257670706545)
          ·
            refine ⟨6447441273530443253029909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8596588364707257670706545 6447441273530443253029909)
            ·
              refine ⟨302223809696739527485777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6447441273530443253029909 302223809696739527485777)
              ·
                refine ⟨226667857272554645614333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 302223809696739527485777 226667857272554645614333)
                ·
                  refine ⟨85000446477207992105375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 226667857272554645614333 85000446477207992105375)
                  ·
                    rfl

theorem cell21_372460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6, 2, 3].length) (baseStart_372460 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_372460 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_372460 prefixEnd_372460 := by exact prefixLift 372460
  have htrace : WordTrace (prefixWord ++ tailWord_372460) baseStart_372460 baseEnd_372460 := by
    simpa [prefixWord, tailWord_372460, baseEnd_372460] using wordTrace_append hprefix tailTrace_372460
  have hstable : (prefixWord ++ tailWord_372460).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372460).length < 2 ^ (prefixWord ++ tailWord_372460).sum := by decide
  have hdescent : baseEnd_372460 < baseStart_372460 := by decide
  rcases family_descends (prefixWord ++ tailWord_372460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372471 : List Nat := [1, 1, 3, 1, 1, 1, 7, 6]
def baseStart_372471 : Nat := 118140960795 + 372471 * 2 ^ 59
def prefixEnd_372471 : Nat := 4983230072969 + 3 ^ 40 * 372471 * 2
def baseEnd_372471 : Nat := 28334318942358139140673

theorem tailTrace_372471 : CollatzResearch.WordTrace tailWord_372471 prefixEnd_372471 28334318942358139140673 := by
  unfold tailWord_372471
  simp only [CollatzResearch.WordTrace]
  refine ⟨13585133433608654827421267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9056755622405769884947511 13585133433608654827421267)
  ·
    refine ⟨20377700150412982241131901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13585133433608654827421267 20377700150412982241131901)
    ·
      refine ⟨7641637556404868340424463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20377700150412982241131901 7641637556404868340424463)
      ·
        refine ⟨11462456334607302510636695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7641637556404868340424463 11462456334607302510636695)
        ·
          refine ⟨17193684501910953765955043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11462456334607302510636695 17193684501910953765955043)
          ·
            refine ⟨25790526752866430648932565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17193684501910953765955043 25790526752866430648932565)
            ·
              refine ⟨604465470770306968334357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 25790526752866430648932565 604465470770306968334357)
              ·
                refine ⟨28334318942358139140673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 604465470770306968334357 28334318942358139140673)
                ·
                  rfl

theorem cell21_372471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 6].length) (baseStart_372471 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_372471 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_372471 prefixEnd_372471 := by exact prefixLift 372471
  have htrace : WordTrace (prefixWord ++ tailWord_372471) baseStart_372471 baseEnd_372471 := by
    simpa [prefixWord, tailWord_372471, baseEnd_372471] using wordTrace_append hprefix tailTrace_372471
  have hstable : (prefixWord ++ tailWord_372471).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372471).length < 2 ^ (prefixWord ++ tailWord_372471).sum := by decide
  have hdescent : baseEnd_372471 < baseStart_372471 := by decide
  rcases family_descends (prefixWord ++ tailWord_372471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372488 : List Nat := [2, 1, 3, 2, 2, 1, 5, 5]
def baseStart_372488 : Nat := 118140960795 + 372488 * 2 ^ 59
def prefixEnd_372488 : Nat := 4983230072969 + 3 ^ 40 * 372488 * 2
def baseEnd_372488 : Nat := 28335612152895388546217

theorem tailTrace_372488 : CollatzResearch.WordTrace tailWord_372488 prefixEnd_372488 28335612152895388546217 := by
  unfold tailWord_372488
  simp only [CollatzResearch.WordTrace]
  refine ⟨6792876737273533365395059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9057168983031377820526745 6792876737273533365395059)
  ·
    refine ⟨10189315105910300048092589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6792876737273533365395059 10189315105910300048092589)
    ·
      refine ⟨3820993164716362518034721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10189315105910300048092589 3820993164716362518034721)
      ·
        refine ⟨2865744873537271888526041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3820993164716362518034721 2865744873537271888526041)
        ·
          refine ⟨2149308655152953916394531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2865744873537271888526041 2149308655152953916394531)
          ·
            refine ⟨3223962982729430874591797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2149308655152953916394531 3223962982729430874591797)
            ·
              refine ⟨302246529630884144492981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3223962982729430874591797 302246529630884144492981)
              ·
                refine ⟨28335612152895388546217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 302246529630884144492981 28335612152895388546217)
                ·
                  rfl

theorem cell21_372488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5, 5].length) (baseStart_372488 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_372488 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_372488 prefixEnd_372488 := by exact prefixLift 372488
  have htrace : WordTrace (prefixWord ++ tailWord_372488) baseStart_372488 baseEnd_372488 := by
    simpa [prefixWord, tailWord_372488, baseEnd_372488] using wordTrace_append hprefix tailTrace_372488
  have hstable : (prefixWord ++ tailWord_372488).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372488).length < 2 ^ (prefixWord ++ tailWord_372488).sum := by decide
  have hdescent : baseEnd_372488 < baseStart_372488 := by decide
  rcases family_descends (prefixWord ++ tailWord_372488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372547 : List Nat := [1, 1, 1, 3, 1, 6, 1, 7]
def baseStart_372547 : Nat := 118140960795 + 372547 * 2 ^ 59
def prefixEnd_372547 : Nat := 4983230072969 + 3 ^ 40 * 372547 * 2
def baseEnd_372547 : Nat := 28340100354171724718399

theorem tailTrace_372547 : CollatzResearch.WordTrace tailWord_372547 prefixEnd_372547 28340100354171724718399 := by
  unfold tailWord_372547
  simp only [CollatzResearch.WordTrace]
  refine ⟨13587905381333319807187895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9058603587555546538125263 13587905381333319807187895)
  ·
    refine ⟨20381858071999979710781843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13587905381333319807187895 20381858071999979710781843)
    ·
      refine ⟨30572787107999969566172765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20381858071999979710781843 30572787107999969566172765)
      ·
        refine ⟨11464795165499988587314787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30572787107999969566172765 11464795165499988587314787)
        ·
          refine ⟨17197192748249982880972181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11464795165499988587314787 17197192748249982880972181)
          ·
            refine ⟨806118410074217947545571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17197192748249982880972181 806118410074217947545571)
            ·
              refine ⟨1209177615111326921318357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 806118410074217947545571 1209177615111326921318357)
              ·
                refine ⟨28340100354171724718399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1209177615111326921318357 28340100354171724718399)
                ·
                  rfl

theorem cell21_372547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 7].length) (baseStart_372547 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_372547 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_372547 prefixEnd_372547 := by exact prefixLift 372547
  have htrace : WordTrace (prefixWord ++ tailWord_372547) baseStart_372547 baseEnd_372547 := by
    simpa [prefixWord, tailWord_372547, baseEnd_372547] using wordTrace_append hprefix tailTrace_372547
  have hstable : (prefixWord ++ tailWord_372547).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372547).length < 2 ^ (prefixWord ++ tailWord_372547).sum := by decide
  have hdescent : baseEnd_372547 < baseStart_372547 := by decide
  rcases family_descends (prefixWord ++ tailWord_372547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372564 : List Nat := [2, 4, 1, 1, 3, 3, 7]
def baseStart_372564 : Nat := 118140960795 + 372564 * 2 ^ 59
def prefixEnd_372564 : Nat := 4983230072969 + 3 ^ 40 * 372564 * 2
def baseEnd_372564 : Nat := 9447131188236324707981

theorem tailTrace_372564 : CollatzResearch.WordTrace tailWord_372564 prefixEnd_372564 9447131188236324707981 := by
  unfold tailWord_372564
  simp only [CollatzResearch.WordTrace]
  refine ⟨6794262711135865855278373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9059016948181154473704497 6794262711135865855278373)
  ·
    refine ⟨1273924258337974847864695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6794262711135865855278373 1273924258337974847864695)
    ·
      refine ⟨1910886387506962271797043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1273924258337974847864695 1910886387506962271797043)
      ·
        refine ⟨2866329581260443407695565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1910886387506962271797043 2866329581260443407695565)
        ·
          refine ⟨1074873592972666277885837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2866329581260443407695565 1074873592972666277885837)
          ·
            refine ⟨403077597364749854207189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1074873592972666277885837 403077597364749854207189)
            ·
              refine ⟨9447131188236324707981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 403077597364749854207189 9447131188236324707981)
              ·
                rfl

theorem cell21_372564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 7].length) (baseStart_372564 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_372564 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_372564 prefixEnd_372564 := by exact prefixLift 372564
  have htrace : WordTrace (prefixWord ++ tailWord_372564) baseStart_372564 baseEnd_372564 := by
    simpa [prefixWord, tailWord_372564, baseEnd_372564] using wordTrace_append hprefix tailTrace_372564
  have hstable : (prefixWord ++ tailWord_372564).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372564).length < 2 ^ (prefixWord ++ tailWord_372564).sum := by decide
  have hdescent : baseEnd_372564 < baseStart_372564 := by decide
  rcases family_descends (prefixWord ++ tailWord_372564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372626 : List Nat := [3, 2, 3, 2, 1, 1, 1, 4, 4]
def baseStart_372626 : Nat := 118140960795 + 372626 * 2 ^ 59
def prefixEnd_372626 : Nat := 4983230072969 + 3 ^ 40 * 372626 * 2
def baseEnd_372626 : Nat := 85038329938828592338369

theorem tailTrace_372626 : CollatzResearch.WordTrace tailWord_372626 prefixEnd_372626 85038329938828592338369 := by
  unfold tailWord_372626
  simp only [CollatzResearch.WordTrace]
  refine ⟨3397696687011779074828433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9060524498698077532875821 3397696687011779074828433)
  ·
    refine ⟨2548272515258834306121325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3397696687011779074828433 2548272515258834306121325)
    ·
      refine ⟨955602193222062864795497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2548272515258834306121325 955602193222062864795497)
      ·
        refine ⟨716701644916547148596623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 955602193222062864795497 716701644916547148596623)
        ·
          refine ⟨1075052467374820722894935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 716701644916547148596623 1075052467374820722894935)
          ·
            refine ⟨1612578701062231084342403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1075052467374820722894935 1612578701062231084342403)
            ·
              refine ⟨2418868051593346626513605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1612578701062231084342403 2418868051593346626513605)
              ·
                refine ⟨453537759673752492471301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2418868051593346626513605 453537759673752492471301)
                ·
                  refine ⟨85038329938828592338369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 453537759673752492471301 85038329938828592338369)
                  ·
                    rfl

theorem cell21_372626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_372626 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_372626 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_372626 prefixEnd_372626 := by exact prefixLift 372626
  have htrace : WordTrace (prefixWord ++ tailWord_372626) baseStart_372626 baseEnd_372626 := by
    simpa [prefixWord, tailWord_372626, baseEnd_372626] using wordTrace_append hprefix tailTrace_372626
  have hstable : (prefixWord ++ tailWord_372626).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372626).length < 2 ^ (prefixWord ++ tailWord_372626).sum := by decide
  have hdescent : baseEnd_372626 < baseStart_372626 := by decide
  rcases family_descends (prefixWord ++ tailWord_372626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372671 : List Nat := [1, 1, 2, 2, 2, 1, 6, 3, 3]
def baseStart_372671 : Nat := 118140960795 + 372671 * 2 ^ 59
def prefixEnd_372671 : Nat := 4983230072969 + 3 ^ 40 * 372671 * 2
def baseEnd_372671 : Nat := 85048599551918514088277

theorem tailTrace_372671 : CollatzResearch.WordTrace tailWord_372671 prefixEnd_372671 85048599551918514088277 := by
  unfold tailWord_372671
  simp only [CollatzResearch.WordTrace]
  refine ⟨13592428032884088984701867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9061618688589392656467911 13592428032884088984701867)
  ·
    refine ⟨20388642049326133477052801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13592428032884088984701867 20388642049326133477052801)
    ·
      refine ⟨15291481536994600107789601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20388642049326133477052801 15291481536994600107789601)
      ·
        refine ⟨11468611152745950080842201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15291481536994600107789601 11468611152745950080842201)
        ·
          refine ⟨8601458364559462560631651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11468611152745950080842201 8601458364559462560631651)
          ·
            refine ⟨12902187546839193840947477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8601458364559462560631651 12902187546839193840947477)
            ·
              refine ⟨604790041258087211294413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12902187546839193840947477 604790041258087211294413)
              ·
                refine ⟨226796265471782704235405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 604790041258087211294413 226796265471782704235405)
                ·
                  refine ⟨85048599551918514088277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 226796265471782704235405 85048599551918514088277)
                  ·
                    rfl

theorem cell21_372671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 3, 3].length) (baseStart_372671 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_372671 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_372671 prefixEnd_372671 := by exact prefixLift 372671
  have htrace : WordTrace (prefixWord ++ tailWord_372671) baseStart_372671 baseEnd_372671 := by
    simpa [prefixWord, tailWord_372671, baseEnd_372671] using wordTrace_append hprefix tailTrace_372671
  have hstable : (prefixWord ++ tailWord_372671).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372671).length < 2 ^ (prefixWord ++ tailWord_372671).sum := by decide
  have hdescent : baseEnd_372671 < baseStart_372671 := by decide
  rcases family_descends (prefixWord ++ tailWord_372671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372744 : List Nat := [2, 1, 3, 2, 1, 2, 1, 3, 6]
def baseStart_372744 : Nat := 118140960795 + 372744 * 2 ^ 59
def prefixEnd_372744 : Nat := 4983230072969 + 3 ^ 40 * 372744 * 2
def baseEnd_372744 : Nat := 85065259146486609371461

theorem tailTrace_372744 : CollatzResearch.WordTrace tailWord_372744 prefixEnd_372744 85065259146486609371461 := by
  unfold tailWord_372744
  simp only [CollatzResearch.WordTrace]
  refine ⟨6797545280809811226054643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9063393707746414968072857 6797545280809811226054643)
  ·
    refine ⟨10196317921214716839081965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6797545280809811226054643 10196317921214716839081965)
    ·
      refine ⟨3823619220455518814655737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10196317921214716839081965 3823619220455518814655737)
      ·
        refine ⟨2867714415341639110991803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3823619220455518814655737 2867714415341639110991803)
        ·
          refine ⟨4301571623012458666487705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2867714415341639110991803 4301571623012458666487705)
          ·
            refine ⟨3226178717259343999865779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4301571623012458666487705 3226178717259343999865779)
            ·
              refine ⟨4839268075889015999798669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3226178717259343999865779 4839268075889015999798669)
              ·
                refine ⟨1814725528458380999924501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4839268075889015999798669 1814725528458380999924501)
                ·
                  refine ⟨85065259146486609371461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1814725528458380999924501 85065259146486609371461)
                  ·
                    rfl

theorem cell21_372744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 6].length) (baseStart_372744 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_372744 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_372744 prefixEnd_372744 := by exact prefixLift 372744
  have htrace : WordTrace (prefixWord ++ tailWord_372744) baseStart_372744 baseEnd_372744 := by
    simpa [prefixWord, tailWord_372744, baseEnd_372744] using wordTrace_append hprefix tailTrace_372744
  have hstable : (prefixWord ++ tailWord_372744).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372744).length < 2 ^ (prefixWord ++ tailWord_372744).sum := by decide
  have hdescent : baseEnd_372744 < baseStart_372744 := by decide
  rcases family_descends (prefixWord ++ tailWord_372744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372798 : List Nat := [4, 2, 1, 3, 2, 2, 2, 2, 3]
def baseStart_372798 : Nat := 118140960795 + 372798 * 2 ^ 59
def prefixEnd_372798 : Nat := 4983230072969 + 3 ^ 40 * 372798 * 2
def baseEnd_372798 : Nat := 85077582682194515471351

theorem tailTrace_372798 : CollatzResearch.WordTrace tailWord_372798 prefixEnd_372798 85077582682194515471351 := by
  unfold tailWord_372798
  simp only [CollatzResearch.WordTrace]
  refine ⟨1699632512927998709321881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9064706735615993116383365 1699632512927998709321881)
  ·
    refine ⟨1274724384695999031991411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1699632512927998709321881 1274724384695999031991411)
    ·
      refine ⟨1912086577043998547987117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1274724384695999031991411 1912086577043998547987117)
      ·
        refine ⟨717032466391499455495169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1912086577043998547987117 717032466391499455495169)
        ·
          refine ⟨537774349793624591621377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 717032466391499455495169 537774349793624591621377)
          ·
            refine ⟨403330762345218443716033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 537774349793624591621377 403330762345218443716033)
            ·
              refine ⟨302498071758913832787025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 403330762345218443716033 302498071758913832787025)
              ·
                refine ⟨226873553819185374590269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 302498071758913832787025 226873553819185374590269)
                ·
                  refine ⟨85077582682194515471351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 226873553819185374590269 85077582682194515471351)
                  ·
                    rfl

theorem cell21_372798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_372798 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_372798 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_372798 prefixEnd_372798 := by exact prefixLift 372798
  have htrace : WordTrace (prefixWord ++ tailWord_372798) baseStart_372798 baseEnd_372798 := by
    simpa [prefixWord, tailWord_372798, baseEnd_372798] using wordTrace_append hprefix tailTrace_372798
  have hstable : (prefixWord ++ tailWord_372798).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372798).length < 2 ^ (prefixWord ++ tailWord_372798).sum := by decide
  have hdescent : baseEnd_372798 < baseStart_372798 := by decide
  rcases family_descends (prefixWord ++ tailWord_372798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372820 : List Nat := [2, 4, 1, 1, 1, 1, 1, 2, 8]
def baseStart_372820 : Nat := 118140960795 + 372820 * 2 ^ 59
def prefixEnd_372820 : Nat := 4983230072969 + 3 ^ 40 * 372820 * 2
def baseEnd_372820 : Nat := 85082603381927366104639

theorem tailTrace_372820 : CollatzResearch.WordTrace tailWord_372820 prefixEnd_372820 85082603381927366104639 := by
  unfold tailWord_372820
  simp only [CollatzResearch.WordTrace]
  refine ⟨6798931254672143715937957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9065241672896191621250609 6798931254672143715937957)
  ·
    refine ⟨1274799610251026946738367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6798931254672143715937957 1274799610251026946738367)
    ·
      refine ⟨1912199415376540420107551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1274799610251026946738367 1912199415376540420107551)
      ·
        refine ⟨2868299123064810630161327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1912199415376540420107551 2868299123064810630161327)
        ·
          refine ⟨4302448684597215945241991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2868299123064810630161327 4302448684597215945241991)
          ·
            refine ⟨6453673026895823917862987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4302448684597215945241991 6453673026895823917862987)
            ·
              refine ⟨9680509540343735876794481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6453673026895823917862987 9680509540343735876794481)
              ·
                refine ⟨7260382155257801907595861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9680509540343735876794481 7260382155257801907595861)
                ·
                  refine ⟨85082603381927366104639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7260382155257801907595861 85082603381927366104639)
                  ·
                    rfl

theorem cell21_372820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_372820 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_372820 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_372820 prefixEnd_372820 := by exact prefixLift 372820
  have htrace : WordTrace (prefixWord ++ tailWord_372820) baseStart_372820 baseEnd_372820 := by
    simpa [prefixWord, tailWord_372820, baseEnd_372820] using wordTrace_append hprefix tailTrace_372820
  have hstable : (prefixWord ++ tailWord_372820).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372820).length < 2 ^ (prefixWord ++ tailWord_372820).sum := by decide
  have hdescent : baseEnd_372820 < baseStart_372820 := by decide
  rcases family_descends (prefixWord ++ tailWord_372820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372854 : List Nat := [5, 1, 1, 2, 1, 2, 3, 2, 4]
def baseStart_372854 : Nat := 118140960795 + 372854 * 2 ^ 59
def prefixEnd_372854 : Nat := 4983230072969 + 3 ^ 40 * 372854 * 2
def baseEnd_372854 : Nat := 85090362645150862537903

theorem tailTrace_372854 : CollatzResearch.WordTrace tailWord_372854 prefixEnd_372854 85090362645150862537903 := by
  unfold tailWord_372854
  simp only [CollatzResearch.WordTrace]
  refine ⟨849943911951319452413351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9066068394147407492409077 849943911951319452413351)
  ·
    refine ⟨1274915867926979178620027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 849943911951319452413351 1274915867926979178620027)
    ·
      refine ⟨1912373801890468767930041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1274915867926979178620027 1912373801890468767930041)
      ·
        refine ⟨1434280351417851575947531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1912373801890468767930041 1434280351417851575947531)
        ·
          refine ⟨2151420527126777363921297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1434280351417851575947531 2151420527126777363921297)
          ·
            refine ⟨1613565395345083022940973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2151420527126777363921297 1613565395345083022940973)
            ·
              refine ⟨605087023254406133602865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1613565395345083022940973 605087023254406133602865)
              ·
                refine ⟨453815267440804600202149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 605087023254406133602865 453815267440804600202149)
                ·
                  refine ⟨85090362645150862537903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 453815267440804600202149 85090362645150862537903)
                  ·
                    rfl

theorem cell21_372854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_372854 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_372854 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_372854 prefixEnd_372854 := by exact prefixLift 372854
  have htrace : WordTrace (prefixWord ++ tailWord_372854) baseStart_372854 baseEnd_372854 := by
    simpa [prefixWord, tailWord_372854, baseEnd_372854] using wordTrace_append hprefix tailTrace_372854
  have hstable : (prefixWord ++ tailWord_372854).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372854).length < 2 ^ (prefixWord ++ tailWord_372854).sum := by decide
  have hdescent : baseEnd_372854 < baseStart_372854 := by decide
  rcases family_descends (prefixWord ++ tailWord_372854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372882 : List Nat := [3, 2, 3, 1, 1, 1, 1, 4, 5]
def baseStart_372882 : Nat := 118140960795 + 372882 * 2 ^ 59
def prefixEnd_372882 : Nat := 4983230072969 + 3 ^ 40 * 372882 * 2
def baseEnd_372882 : Nat := 85096752626629036071179

theorem tailTrace_372882 : CollatzResearch.WordTrace tailWord_372882 prefixEnd_372882 85096752626629036071179 := by
  unfold tailWord_372882
  simp only [CollatzResearch.WordTrace]
  refine ⟨3400030958779918005158225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9066749223413114680421933 3400030958779918005158225)
  ·
    refine ⟨2550023219084938503868669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3400030958779918005158225 2550023219084938503868669)
    ·
      refine ⟨956258707156851938950751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2550023219084938503868669 956258707156851938950751)
      ·
        refine ⟨1434388060735277908426127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 956258707156851938950751 1434388060735277908426127)
        ·
          refine ⟨2151582091102916862639191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1434388060735277908426127 2151582091102916862639191)
          ·
            refine ⟨3227373136654375293958787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2151582091102916862639191 3227373136654375293958787)
            ·
              refine ⟨4841059704981562940938181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3227373136654375293958787 4841059704981562940938181)
              ·
                refine ⟨907698694684043051425909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4841059704981562940938181 907698694684043051425909)
                ·
                  refine ⟨85096752626629036071179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 907698694684043051425909 85096752626629036071179)
                  ·
                    rfl

theorem cell21_372882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_372882 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_372882 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_372882 prefixEnd_372882 := by exact prefixLift 372882
  have htrace : WordTrace (prefixWord ++ tailWord_372882) baseStart_372882 baseEnd_372882 := by
    simpa [prefixWord, tailWord_372882, baseEnd_372882] using wordTrace_append hprefix tailTrace_372882
  have hstable : (prefixWord ++ tailWord_372882).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372882).length < 2 ^ (prefixWord ++ tailWord_372882).sum := by decide
  have hdescent : baseEnd_372882 < baseStart_372882 := by decide
  rcases family_descends (prefixWord ++ tailWord_372882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372896 : List Nat := [2, 1, 1, 4, 2, 2, 1, 2, 6]
def baseStart_372896 : Nat := 118140960795 + 372896 * 2 ^ 59
def prefixEnd_372896 : Nat := 4983230072969 + 3 ^ 40 * 372896 * 2
def baseEnd_372896 : Nat := 85099947617368122837817

theorem tailTrace_372896 : CollatzResearch.WordTrace tailWord_372896 prefixEnd_372896 85099947617368122837817 := by
  unfold tailWord_372896
  simp only [CollatzResearch.WordTrace]
  refine ⟨6800317228534476205821271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9067089638045968274428361 6800317228534476205821271)
  ·
    refine ⟨10200475842801714308731907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6800317228534476205821271 10200475842801714308731907)
    ·
      refine ⟨15300713764202571463097861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10200475842801714308731907 15300713764202571463097861)
      ·
        refine ⟨2868883830787982149330849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15300713764202571463097861 2868883830787982149330849)
        ·
          refine ⟨2151662873090986611998137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2868883830787982149330849 2151662873090986611998137)
          ·
            refine ⟨1613747154818239958998603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2151662873090986611998137 1613747154818239958998603)
            ·
              refine ⟨2420620732227359938497905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1613747154818239958998603 2420620732227359938497905)
              ·
                refine ⟨1815465549170519953873429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2420620732227359938497905 1815465549170519953873429)
                ·
                  refine ⟨85099947617368122837817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1815465549170519953873429 85099947617368122837817)
                  ·
                    rfl

theorem cell21_372896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 6].length) (baseStart_372896 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_372896 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_372896 prefixEnd_372896 := by exact prefixLift 372896
  have htrace : WordTrace (prefixWord ++ tailWord_372896) baseStart_372896 baseEnd_372896 := by
    simpa [prefixWord, tailWord_372896, baseEnd_372896] using wordTrace_append hprefix tailTrace_372896
  have hstable : (prefixWord ++ tailWord_372896).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372896).length < 2 ^ (prefixWord ++ tailWord_372896).sum := by decide
  have hdescent : baseEnd_372896 < baseStart_372896 := by decide
  rcases family_descends (prefixWord ++ tailWord_372896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372975 : List Nat := [1, 1, 2, 1, 6, 2, 1, 4, 3]
def baseStart_372975 : Nat := 118140960795 + 372975 * 2 ^ 59
def prefixEnd_372975 : Nat := 4983230072969 + 3 ^ 40 * 372975 * 2
def baseEnd_372975 : Nat := 85117976493681541020989

theorem tailTrace_372975 : CollatzResearch.WordTrace tailWord_372975 prefixEnd_372975 85117976493681541020989 := by
  unfold tailWord_372975
  simp only [CollatzResearch.WordTrace]
  refine ⟨13603515823782748903768379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9069010549188499269178919 13603515823782748903768379)
  ·
    refine ⟨20405273735674123355652569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13603515823782748903768379 20405273735674123355652569)
    ·
      refine ⟨15303955301755592516739427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20405273735674123355652569 15303955301755592516739427)
      ·
        refine ⟨22955932952633388775109141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15303955301755592516739427 22955932952633388775109141)
        ·
          refine ⟨1076059357154690098833241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 22955932952633388775109141 1076059357154690098833241)
          ·
            refine ⟨807044517866017574124931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1076059357154690098833241 807044517866017574124931)
            ·
              refine ⟨1210566776799026361187397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 807044517866017574124931 1210566776799026361187397)
              ·
                refine ⟨226981270649817442722637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1210566776799026361187397 226981270649817442722637)
                ·
                  refine ⟨85117976493681541020989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 226981270649817442722637 85117976493681541020989)
                  ·
                    rfl

theorem cell21_372975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 4, 3].length) (baseStart_372975 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_372975 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_372975 prefixEnd_372975 := by exact prefixLift 372975
  have htrace : WordTrace (prefixWord ++ tailWord_372975) baseStart_372975 baseEnd_372975 := by
    simpa [prefixWord, tailWord_372975, baseEnd_372975] using wordTrace_append hprefix tailTrace_372975
  have hstable : (prefixWord ++ tailWord_372975).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372975).length < 2 ^ (prefixWord ++ tailWord_372975).sum := by decide
  have hdescent : baseEnd_372975 < baseStart_372975 := by decide
  rcases family_descends (prefixWord ++ tailWord_372975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373003 : List Nat := [1, 1, 1, 1, 5, 2, 5, 5]
def baseStart_373003 : Nat := 118140960795 + 373003 * 2 ^ 59
def prefixEnd_373003 : Nat := 4983230072969 + 3 ^ 40 * 373003 * 2
def baseEnd_373003 : Nat := 28374788825053238184755

theorem tailTrace_373003 : CollatzResearch.WordTrace tailWord_373003 prefixEnd_373003 28374788825053238184755 := by
  unfold tailWord_373003
  simp only [CollatzResearch.WordTrace]
  refine ⟨13604537067681309685787663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9069691378454206457191775 13604537067681309685787663)
  ·
    refine ⟨20406805601521964528681495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13604537067681309685787663 20406805601521964528681495)
    ·
      refine ⟨30610208402282946793022243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20406805601521964528681495 30610208402282946793022243)
      ·
        refine ⟨45915312603424420189533365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30610208402282946793022243 45915312603424420189533365)
        ·
          refine ⟨4304560556571039392768753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45915312603424420189533365 4304560556571039392768753)
          ·
            refine ⟨3228420417428279544576565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4304560556571039392768753 3228420417428279544576565)
            ·
              refine ⟨302664414133901207304053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3228420417428279544576565 302664414133901207304053)
              ·
                refine ⟨28374788825053238184755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 302664414133901207304053 28374788825053238184755)
                ·
                  rfl

theorem cell21_373003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5, 5].length) (baseStart_373003 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_373003 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_373003 prefixEnd_373003 := by exact prefixLift 373003
  have htrace : WordTrace (prefixWord ++ tailWord_373003) baseStart_373003 baseEnd_373003 := by
    simpa [prefixWord, tailWord_373003, baseEnd_373003] using wordTrace_append hprefix tailTrace_373003
  have hstable : (prefixWord ++ tailWord_373003).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373003).length < 2 ^ (prefixWord ++ tailWord_373003).sum := by decide
  have hdescent : baseEnd_373003 < baseStart_373003 := by decide
  rcases family_descends (prefixWord ++ tailWord_373003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373048 : List Nat := [2, 1, 2, 1, 3, 1, 2, 5, 4]
def baseStart_373048 : Nat := 118140960795 + 373048 * 2 ^ 59
def prefixEnd_373048 : Nat := 4983230072969 + 3 ^ 40 * 373048 * 2
def baseEnd_373048 : Nat := 85134636088249636304173

theorem tailTrace_373048 : CollatzResearch.WordTrace tailWord_373048 prefixEnd_373048 85134636088249636304173 := by
  unfold tailWord_373048
  simp only [CollatzResearch.WordTrace]
  refine ⟨6803089176259141185587899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9070785568345521580783865 6803089176259141185587899)
  ·
    refine ⟨10204633764388711778381849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6803089176259141185587899 10204633764388711778381849)
    ·
      refine ⟨7653475323291533833786387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10204633764388711778381849 7653475323291533833786387)
      ·
        refine ⟨11480212984937300750679581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7653475323291533833786387 11480212984937300750679581)
        ·
          refine ⟨4305079869351487781504843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11480212984937300750679581 4305079869351487781504843)
          ·
            refine ⟨6457619804027231672257265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4305079869351487781504843 6457619804027231672257265)
            ·
              refine ⟨4843214853020423754192949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6457619804027231672257265 4843214853020423754192949)
              ·
                refine ⟨454051392470664726955589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4843214853020423754192949 454051392470664726955589)
                ·
                  refine ⟨85134636088249636304173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 454051392470664726955589 85134636088249636304173)
                  ·
                    rfl

theorem cell21_373048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 5, 4].length) (baseStart_373048 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_373048 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_373048 prefixEnd_373048 := by exact prefixLift 373048
  have htrace : WordTrace (prefixWord ++ tailWord_373048) baseStart_373048 baseEnd_373048 := by
    simpa [prefixWord, tailWord_373048, baseEnd_373048] using wordTrace_append hprefix tailTrace_373048
  have hstable : (prefixWord ++ tailWord_373048).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373048).length < 2 ^ (prefixWord ++ tailWord_373048).sum := by decide
  have hdescent : baseEnd_373048 < baseStart_373048 := by decide
  rcases family_descends (prefixWord ++ tailWord_373048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373138 : List Nat := [3, 2, 3, 13]
def baseStart_373138 : Nat := 118140960795 + 373138 * 2 ^ 59
def prefixEnd_373138 : Nat := 4983230072969 + 3 ^ 40 * 373138 * 2
def baseEnd_373138 : Nat := 350432820223989628823

theorem tailTrace_373138 : CollatzResearch.WordTrace tailWord_373138 prefixEnd_373138 350432820223989628823 := by
  unfold tailWord_373138
  simp only [CollatzResearch.WordTrace]
  refine ⟨3402365230548056935488017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9072973948128151827968045 3402365230548056935488017)
  ·
    refine ⟨2551773922911042701616013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3402365230548056935488017 2551773922911042701616013)
    ·
      refine ⟨956915221091641013106005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2551773922911042701616013 956915221091641013106005)
      ·
        refine ⟨350432820223989628823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 956915221091641013106005 350432820223989628823)
        ·
          rfl

theorem cell21_373138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 13].length) (baseStart_373138 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_373138 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_373138 prefixEnd_373138 := by exact prefixLift 373138
  have htrace : WordTrace (prefixWord ++ tailWord_373138) baseStart_373138 baseEnd_373138 := by
    simpa [prefixWord, tailWord_373138, baseEnd_373138] using wordTrace_append hprefix tailTrace_373138
  have hstable : (prefixWord ++ tailWord_373138).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373138).length < 2 ^ (prefixWord ++ tailWord_373138).sum := by decide
  have hdescent : baseEnd_373138 < baseStart_373138 := by decide
  rcases family_descends (prefixWord ++ tailWord_373138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373144 : List Nat := [2, 1, 2, 5, 1, 1, 4, 2, 3]
def baseStart_373144 : Nat := 118140960795 + 373144 * 2 ^ 59
def prefixEnd_373144 : Nat := 4983230072969 + 3 ^ 40 * 373144 * 2
def baseEnd_373144 : Nat := 85156544596174802703977

theorem tailTrace_373144 : CollatzResearch.WordTrace tailWord_373144 prefixEnd_373144 85156544596174802703977 := by
  unfold tailWord_373144
  simp only [CollatzResearch.WordTrace]
  refine ⟨6804839880085245383335243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9073119840113660511113657 6804839880085245383335243)
  ·
    refine ⟨10207259820127868075002865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6804839880085245383335243 10207259820127868075002865)
    ·
      refine ⟨7655444865095901056252149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10207259820127868075002865 7655444865095901056252149)
      ·
        refine ⟨717697956102740724023639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7655444865095901056252149 717697956102740724023639)
        ·
          refine ⟨1076546934154111086035459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 717697956102740724023639 1076546934154111086035459)
          ·
            refine ⟨1614820401231166629053189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1076546934154111086035459 1614820401231166629053189)
            ·
              refine ⟨302778825230843742947473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1614820401231166629053189 302778825230843742947473)
              ·
                refine ⟨227084118923132807210605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 302778825230843742947473 227084118923132807210605)
                ·
                  refine ⟨85156544596174802703977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 227084118923132807210605 85156544596174802703977)
                  ·
                    rfl

theorem cell21_373144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4, 2, 3].length) (baseStart_373144 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_373144 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_373144 prefixEnd_373144 := by exact prefixLift 373144
  have htrace : WordTrace (prefixWord ++ tailWord_373144) baseStart_373144 baseEnd_373144 := by
    simpa [prefixWord, tailWord_373144, baseEnd_373144] using wordTrace_append hprefix tailTrace_373144
  have hstable : (prefixWord ++ tailWord_373144).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373144).length < 2 ^ (prefixWord ++ tailWord_373144).sum := by decide
  have hdescent : baseEnd_373144 < baseStart_373144 := by decide
  rcases family_descends (prefixWord ++ tailWord_373144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373155 : List Nat := [1, 1, 1, 4, 1, 6, 1, 6]
def baseStart_373155 : Nat := 118140960795 + 373155 * 2 ^ 59
def prefixEnd_373155 : Nat := 4983230072969 + 3 ^ 40 * 373155 * 2
def baseEnd_373155 : Nat := 28386351648680409340207

theorem tailTrace_373155 : CollatzResearch.WordTrace tailWord_373155 prefixEnd_373155 28386351648680409340207 := by
  unfold tailWord_373155
  simp only [CollatzResearch.WordTrace]
  refine ⟨13610080963130639645320919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9073387308753759763547279 13610080963130639645320919)
  ·
    refine ⟨20415121444695959467981379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13610080963130639645320919 20415121444695959467981379)
    ·
      refine ⟨30622682167043939201972069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20415121444695959467981379 30622682167043939201972069)
      ·
        refine ⟨5741752906320738600369763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30622682167043939201972069 5741752906320738600369763)
        ·
          refine ⟨8612629359481107900554645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5741752906320738600369763 8612629359481107900554645)
          ·
            refine ⟨403717001225676932838499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8612629359481107900554645 403717001225676932838499)
            ·
              refine ⟨605575501838515399257749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 403717001225676932838499 605575501838515399257749)
              ·
                refine ⟨28386351648680409340207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 605575501838515399257749 28386351648680409340207)
                ·
                  rfl

theorem cell21_373155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 6].length) (baseStart_373155 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_373155 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_373155 prefixEnd_373155 := by exact prefixLift 373155
  have htrace : WordTrace (prefixWord ++ tailWord_373155) baseStart_373155 baseEnd_373155 := by
    simpa [prefixWord, tailWord_373155, baseEnd_373155] using wordTrace_append hprefix tailTrace_373155
  have hstable : (prefixWord ++ tailWord_373155).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373155).length < 2 ^ (prefixWord ++ tailWord_373155).sum := by decide
  have hdescent : baseEnd_373155 < baseStart_373155 := by decide
  rcases family_descends (prefixWord ++ tailWord_373155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373169 : List Nat := [1, 2, 2, 4, 1, 2, 1, 1, 7]
def baseStart_373169 : Nat := 118140960795 + 373169 * 2 ^ 59
def prefixEnd_373169 : Nat := 4983230072969 + 3 ^ 40 * 373169 * 2
def baseEnd_373169 : Nat := 85162249936780314787259

theorem tailTrace_373169 : CollatzResearch.WordTrace tailWord_373169 prefixEnd_373169 85162249936780314787259 := by
  unfold tailWord_373169
  simp only [CollatzResearch.WordTrace]
  refine ⟨13610591585079920036330561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9073727723386613357553707 13610591585079920036330561)
  ·
    refine ⟨10207943688809940027247921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13610591585079920036330561 10207943688809940027247921)
    ·
      refine ⟨7655957766607455020435941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10207943688809940027247921 7655957766607455020435941)
      ·
        refine ⟨1435492081238897816331739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7655957766607455020435941 1435492081238897816331739)
        ·
          refine ⟨2153238121858346724497609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1435492081238897816331739 2153238121858346724497609)
          ·
            refine ⟨1614928591393760043373207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2153238121858346724497609 1614928591393760043373207)
            ·
              refine ⟨2422392887090640065059811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1614928591393760043373207 2422392887090640065059811)
              ·
                refine ⟨3633589330635960097589717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2422392887090640065059811 3633589330635960097589717)
                ·
                  refine ⟨85162249936780314787259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3633589330635960097589717 85162249936780314787259)
                  ·
                    rfl

theorem cell21_373169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 7].length) (baseStart_373169 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_373169 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_373169 prefixEnd_373169 := by exact prefixLift 373169
  have htrace : WordTrace (prefixWord ++ tailWord_373169) baseStart_373169 baseEnd_373169 := by
    simpa [prefixWord, tailWord_373169, baseEnd_373169] using wordTrace_append hprefix tailTrace_373169
  have hstable : (prefixWord ++ tailWord_373169).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373169).length < 2 ^ (prefixWord ++ tailWord_373169).sum := by decide
  have hdescent : baseEnd_373169 < baseStart_373169 := by decide
  rcases family_descends (prefixWord ++ tailWord_373169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373217 : List Nat := [1, 2, 3, 1, 2, 2, 5, 1, 4]
def baseStart_373217 : Nat := 118140960795 + 373217 * 2 ^ 59
def prefixEnd_373217 : Nat := 4983230072969 + 3 ^ 40 * 373217 * 2
def baseEnd_373217 : Nat := 85173204190742897987161

theorem tailTrace_373217 : CollatzResearch.WordTrace tailWord_373217 prefixEnd_373217 85173204190742897987161 := by
  unfold tailWord_373217
  simp only [CollatzResearch.WordTrace]
  refine ⟨13612342288906024234077905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9074894859270682822718603 13612342288906024234077905)
  ·
    refine ⟨10209256716679518175558429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13612342288906024234077905 10209256716679518175558429)
    ·
      refine ⟨3828471268754819315834411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10209256716679518175558429 3828471268754819315834411)
      ·
        refine ⟨5742706903132228973751617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3828471268754819315834411 5742706903132228973751617)
        ·
          refine ⟨4307030177349171730313713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5742706903132228973751617 4307030177349171730313713)
          ·
            refine ⟨3230272633011878797735285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4307030177349171730313713 3230272633011878797735285)
            ·
              refine ⟨302838059344863637287683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3230272633011878797735285 302838059344863637287683)
              ·
                refine ⟨454257089017295455931525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 302838059344863637287683 454257089017295455931525)
                ·
                  refine ⟨85173204190742897987161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 454257089017295455931525 85173204190742897987161)
                  ·
                    rfl

theorem cell21_373217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5, 1, 4].length) (baseStart_373217 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_373217 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_373217 prefixEnd_373217 := by exact prefixLift 373217
  have htrace : WordTrace (prefixWord ++ tailWord_373217) baseStart_373217 baseEnd_373217 := by
    simpa [prefixWord, tailWord_373217, baseEnd_373217] using wordTrace_append hprefix tailTrace_373217
  have hstable : (prefixWord ++ tailWord_373217).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373217).length < 2 ^ (prefixWord ++ tailWord_373217).sum := by decide
  have hdescent : baseEnd_373217 < baseStart_373217 := by decide
  rcases family_descends (prefixWord ++ tailWord_373217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373237 : List Nat := [1, 3, 5, 1, 2, 2, 1, 3, 3]
def baseStart_373237 : Nat := 118140960795 + 373237 * 2 ^ 59
def prefixEnd_373237 : Nat := 4983230072969 + 3 ^ 40 * 373237 * 2
def baseEnd_373237 : Nat := 85177768463227307653787

theorem tailTrace_373237 : CollatzResearch.WordTrace tailWord_373237 prefixEnd_373237 85177768463227307653787 := by
  unfold tailWord_373237
  simp only [CollatzResearch.WordTrace]
  refine ⟨13613071748833567649805965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9075381165889045099870643 13613071748833567649805965)
  ·
    refine ⟨5104901905812587868677237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13613071748833567649805965 5104901905812587868677237)
    ·
      refine ⟨478584553669930112688491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5104901905812587868677237 478584553669930112688491)
      ·
        refine ⟨717876830504895169032737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 478584553669930112688491 717876830504895169032737)
        ·
          refine ⟨538407622878671376774553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 717876830504895169032737 538407622878671376774553)
          ·
            refine ⟨403805717159003532580915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 538407622878671376774553 403805717159003532580915)
            ·
              refine ⟨605708575738505298871373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 403805717159003532580915 605708575738505298871373)
              ·
                refine ⟨227140715901939487076765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 605708575738505298871373 227140715901939487076765)
                ·
                  refine ⟨85177768463227307653787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 227140715901939487076765 85177768463227307653787)
                  ·
                    rfl

theorem cell21_373237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 3, 3].length) (baseStart_373237 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_373237 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_373237 prefixEnd_373237 := by exact prefixLift 373237
  have htrace : WordTrace (prefixWord ++ tailWord_373237) baseStart_373237 baseEnd_373237 := by
    simpa [prefixWord, tailWord_373237, baseEnd_373237] using wordTrace_append hprefix tailTrace_373237
  have hstable : (prefixWord ++ tailWord_373237).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373237).length < 2 ^ (prefixWord ++ tailWord_373237).sum := by decide
  have hdescent : baseEnd_373237 < baseStart_373237 := by decide
  rcases family_descends (prefixWord ++ tailWord_373237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373262 : List Nat := [4, 1, 1, 2, 3, 1, 3, 1, 5]
def baseStart_373262 : Nat := 118140960795 + 373262 * 2 ^ 59
def prefixEnd_373262 : Nat := 4983230072969 + 3 ^ 40 * 373262 * 2
def baseEnd_373262 : Nat := 85183473803832819737069

theorem tailTrace_373262 : CollatzResearch.WordTrace tailWord_373262 prefixEnd_373262 85183473803832819737069 := by
  unfold tailWord_373262
  simp only [CollatzResearch.WordTrace]
  refine ⟨1701747946717874614933255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9075989049161997946310693 1701747946717874614933255)
  ·
    refine ⟨2552621920076811922399883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1701747946717874614933255 2552621920076811922399883)
    ·
      refine ⟨3828932880115217883599825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2552621920076811922399883 3828932880115217883599825)
      ·
        refine ⟨2871699660086413412699869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3828932880115217883599825 2871699660086413412699869)
        ·
          refine ⟨1076887372532405029762451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2871699660086413412699869 1076887372532405029762451)
          ·
            refine ⟨1615331058798607544643677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1076887372532405029762451 1615331058798607544643677)
            ·
              refine ⟨605749147049477829241379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1615331058798607544643677 605749147049477829241379)
              ·
                refine ⟨908623720574216743862069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 605749147049477829241379 908623720574216743862069)
                ·
                  refine ⟨85183473803832819737069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 908623720574216743862069 85183473803832819737069)
                  ·
                    rfl

theorem cell21_373262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_373262 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_373262 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_373262 prefixEnd_373262 := by exact prefixLift 373262
  have htrace : WordTrace (prefixWord ++ tailWord_373262) baseStart_373262 baseEnd_373262 := by
    simpa [prefixWord, tailWord_373262, baseEnd_373262] using wordTrace_append hprefix tailTrace_373262
  have hstable : (prefixWord ++ tailWord_373262).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373262).length < 2 ^ (prefixWord ++ tailWord_373262).sum := by decide
  have hdescent : baseEnd_373262 < baseStart_373262 := by decide
  rcases family_descends (prefixWord ++ tailWord_373262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373369 : List Nat := [1, 2, 1, 3, 3, 4, 1, 2, 4]
def baseStart_373369 : Nat := 118140960795 + 373369 * 2 ^ 59
def prefixEnd_373369 : Nat := 4983230072969 + 3 ^ 40 * 373369 * 2
def baseEnd_373369 : Nat := 85207892661624411453517

theorem tailTrace_373369 : CollatzResearch.WordTrace tailWord_373369 prefixEnd_373369 85207892661624411453517 := by
  unfold tailWord_373369
  simp only [CollatzResearch.WordTrace]
  refine ⟨13617886184355354193611161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9078590789570236129074107 13617886184355354193611161)
  ·
    refine ⟨10213414638266515645208371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13617886184355354193611161 10213414638266515645208371)
    ·
      refine ⟨15320121957399773467812557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10213414638266515645208371 15320121957399773467812557)
      ·
        refine ⟨5745045734024915050429709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15320121957399773467812557 5745045734024915050429709)
        ·
          refine ⟨2154392150259343143911141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5745045734024915050429709 2154392150259343143911141)
          ·
            refine ⟨403948528173626839483339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2154392150259343143911141 403948528173626839483339)
            ·
              refine ⟨605922792260440259225009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 403948528173626839483339 605922792260440259225009)
              ·
                refine ⟨454442094195330194418757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 605922792260440259225009 454442094195330194418757)
                ·
                  refine ⟨85207892661624411453517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 454442094195330194418757 85207892661624411453517)
                  ·
                    rfl

theorem cell21_373369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 2, 4].length) (baseStart_373369 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_373369 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_373369 prefixEnd_373369 := by exact prefixLift 373369
  have htrace : WordTrace (prefixWord ++ tailWord_373369) baseStart_373369 baseEnd_373369 := by
    simpa [prefixWord, tailWord_373369, baseEnd_373369] using wordTrace_append hprefix tailTrace_373369
  have hstable : (prefixWord ++ tailWord_373369).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373369).length < 2 ^ (prefixWord ++ tailWord_373369).sum := by decide
  have hdescent : baseEnd_373369 < baseStart_373369 := by decide
  rcases family_descends (prefixWord ++ tailWord_373369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373386 : List Nat := [3, 1, 2, 3, 3, 1, 3, 1, 4]
def baseStart_373386 : Nat := 118140960795 + 373386 * 2 ^ 59
def prefixEnd_373386 : Nat := 4983230072969 + 3 ^ 40 * 373386 * 2
def baseEnd_373386 : Nat := 85211772293236159670149

theorem tailTrace_373386 : CollatzResearch.WordTrace tailWord_373386 prefixEnd_373386 85211772293236159670149 := by
  unfold tailWord_373386
  simp only [CollatzResearch.WordTrace]
  refine ⟨3404626556323441524245003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9079004150195844064653341 3404626556323441524245003)
  ·
    refine ⟨5106939834485162286367505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3404626556323441524245003 5106939834485162286367505)
    ·
      refine ⟨3830204875863871714775629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5106939834485162286367505 3830204875863871714775629)
      ·
        refine ⟨1436326828448951893040861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3830204875863871714775629 1436326828448951893040861)
        ·
          refine ⟨538622560668356959890323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1436326828448951893040861 538622560668356959890323)
          ·
            refine ⟨807933841002535439835485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 538622560668356959890323 807933841002535439835485)
            ·
              refine ⟨302975190375950789938307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 807933841002535439835485 302975190375950789938307)
              ·
                refine ⟨454462785563926184907461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 302975190375950789938307 454462785563926184907461)
                ·
                  refine ⟨85211772293236159670149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 454462785563926184907461 85211772293236159670149)
                  ·
                    rfl

theorem cell21_373386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3, 1, 4].length) (baseStart_373386 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_373386 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_373386 prefixEnd_373386 := by exact prefixLift 373386
  have htrace : WordTrace (prefixWord ++ tailWord_373386) baseStart_373386 baseEnd_373386 := by
    simpa [prefixWord, tailWord_373386, baseEnd_373386] using wordTrace_append hprefix tailTrace_373386
  have hstable : (prefixWord ++ tailWord_373386).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373386).length < 2 ^ (prefixWord ++ tailWord_373386).sum := by decide
  have hdescent : baseEnd_373386 < baseStart_373386 := by decide
  rcases family_descends (prefixWord ++ tailWord_373386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373431 : List Nat := [1, 1, 3, 1, 7, 1, 1, 1, 5]
def baseStart_373431 : Nat := 118140960795 + 373431 * 2 ^ 59
def prefixEnd_373431 : Nat := 4983230072969 + 3 ^ 40 * 373431 * 2
def baseEnd_373431 : Nat := 85222041906326081420057

theorem tailTrace_373431 : CollatzResearch.WordTrace tailWord_373431 prefixEnd_373431 85222041906326081420057 := by
  unfold tailWord_373431
  simp only [CollatzResearch.WordTrace]
  refine ⟨13620147510130738782368147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9080098340087159188245431 13620147510130738782368147)
  ·
    refine ⟨20430221265196108173552221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13620147510130738782368147 20430221265196108173552221)
    ·
      refine ⟨7661332974448540565082083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20430221265196108173552221 7661332974448540565082083)
      ·
        refine ⟨11491999461672810847623125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7661332974448540565082083 11491999461672810847623125)
        ·
          refine ⟨269343737382956504241167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 11491999461672810847623125 269343737382956504241167)
          ·
            refine ⟨404015606074434756361751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269343737382956504241167 404015606074434756361751)
            ·
              refine ⟨606023409111652134542627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 404015606074434756361751 606023409111652134542627)
              ·
                refine ⟨909035113667478201813941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 606023409111652134542627 909035113667478201813941)
                ·
                  refine ⟨85222041906326081420057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 909035113667478201813941 85222041906326081420057)
                  ·
                    rfl

theorem cell21_373431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 1, 5].length) (baseStart_373431 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_373431 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_373431 prefixEnd_373431 := by exact prefixLift 373431
  have htrace : WordTrace (prefixWord ++ tailWord_373431) baseStart_373431 baseEnd_373431 := by
    simpa [prefixWord, tailWord_373431, baseEnd_373431] using wordTrace_append hprefix tailTrace_373431
  have hstable : (prefixWord ++ tailWord_373431).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373431).length < 2 ^ (prefixWord ++ tailWord_373431).sum := by decide
  have hdescent : baseEnd_373431 < baseStart_373431 := by decide
  rcases family_descends (prefixWord ++ tailWord_373431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373569 : List Nat := [1, 2, 5, 3, 1, 2, 2, 5]
def baseStart_373569 : Nat := 118140960795 + 373569 * 2 ^ 59
def prefixEnd_373569 : Nat := 4983230072969 + 3 ^ 40 * 373569 * 2
def baseEnd_373569 : Nat := 28417845128822836039925

theorem tailTrace_373569 : CollatzResearch.WordTrace tailWord_373569 prefixEnd_373569 28417845128822836039925 := by
  unfold tailWord_373569
  simp only [CollatzResearch.WordTrace]
  refine ⟨13625180783630788350891761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9083453855753858900594507 13625180783630788350891761)
  ·
    refine ⟨10218885587723091263168821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13625180783630788350891761 10218885587723091263168821)
    ·
      refine ⟨958020523849039805922077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10218885587723091263168821 958020523849039805922077)
      ·
        refine ⟨359257696443389927220779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 958020523849039805922077 359257696443389927220779)
        ·
          refine ⟨538886544665084890831169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359257696443389927220779 538886544665084890831169)
          ·
            refine ⟨404164908498813668123377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 538886544665084890831169 404164908498813668123377)
            ·
              refine ⟨303123681374110251092533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 404164908498813668123377 303123681374110251092533)
              ·
                refine ⟨28417845128822836039925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 303123681374110251092533 28417845128822836039925)
                ·
                  rfl

theorem cell21_373569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2, 5].length) (baseStart_373569 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_373569 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_373569 prefixEnd_373569 := by exact prefixLift 373569
  have htrace : WordTrace (prefixWord ++ tailWord_373569) baseStart_373569 baseEnd_373569 := by
    simpa [prefixWord, tailWord_373569, baseEnd_373569] using wordTrace_append hprefix tailTrace_373569
  have hstable : (prefixWord ++ tailWord_373569).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373569).length < 2 ^ (prefixWord ++ tailWord_373569).sum := by decide
  have hdescent : baseEnd_373569 < baseStart_373569 := by decide
  rcases family_descends (prefixWord ++ tailWord_373569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373594 : List Nat := [3, 1, 1, 2, 1, 6, 7]
def baseStart_373594 : Nat := 118140960795 + 373594 * 2 ^ 59
def prefixEnd_373594 : Nat := 4983230072969 + 3 ^ 40 * 373594 * 2
def baseEnd_373594 : Nat := 9473248969674891133673

theorem tailTrace_373594 : CollatzResearch.WordTrace tailWord_373594 prefixEnd_373594 9473248969674891133673 := by
  unfold tailWord_373594
  simp only [CollatzResearch.WordTrace]
  refine ⟨3406523152135054405137959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9084061739026811747034557 3406523152135054405137959)
  ·
    refine ⟨5109784728202581607706939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3406523152135054405137959 5109784728202581607706939)
    ·
      refine ⟨7664677092303872411560409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5109784728202581607706939 7664677092303872411560409)
      ·
        refine ⟨5748507819227904308670307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7664677092303872411560409 5748507819227904308670307)
        ·
          refine ⟨8622761728841856463005461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5748507819227904308670307 8622761728841856463005461)
          ·
            refine ⟨404191956039462021703381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8622761728841856463005461 404191956039462021703381)
            ·
              refine ⟨9473248969674891133673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 404191956039462021703381 9473248969674891133673)
              ·
                rfl

theorem cell21_373594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 7].length) (baseStart_373594 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_373594 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_373594 prefixEnd_373594 := by exact prefixLift 373594
  have htrace : WordTrace (prefixWord ++ tailWord_373594) baseStart_373594 baseEnd_373594 := by
    simpa [prefixWord, tailWord_373594, baseEnd_373594] using wordTrace_append hprefix tailTrace_373594
  have hstable : (prefixWord ++ tailWord_373594).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373594).length < 2 ^ (prefixWord ++ tailWord_373594).sum := by decide
  have hdescent : baseEnd_373594 < baseStart_373594 := by decide
  rcases family_descends (prefixWord ++ tailWord_373594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373653 : List Nat := [1, 3, 2, 1, 1, 13]
def baseStart_373653 : Nat := 118140960795 + 373653 * 2 ^ 59
def prefixEnd_373653 : Nat := 4983230072969 + 3 ^ 40 * 373653 * 2
def baseEnd_373653 : Nat := 3158248345589001063689

theorem tailTrace_373653 : CollatzResearch.WordTrace tailWord_373653 prefixEnd_373653 3158248345589001063689 := by
  unfold tailWord_373653
  simp only [CollatzResearch.WordTrace]
  refine ⟨13628244515326470696949613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9085496343550980464633075 13628244515326470696949613)
  ·
    refine ⟨5110591693247426511356105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13628244515326470696949613 5110591693247426511356105)
    ·
      refine ⟨3832943769935569883517079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5110591693247426511356105 3832943769935569883517079)
      ·
        refine ⟨5749415654903354825275619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3832943769935569883517079 5749415654903354825275619)
        ·
          refine ⟨8624123482355032237913429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5749415654903354825275619 8624123482355032237913429)
          ·
            refine ⟨3158248345589001063689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 8624123482355032237913429 3158248345589001063689)
            ·
              rfl

theorem cell21_373653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 13].length) (baseStart_373653 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_373653 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_373653 prefixEnd_373653 := by exact prefixLift 373653
  have htrace : WordTrace (prefixWord ++ tailWord_373653) baseStart_373653 baseEnd_373653 := by
    simpa [prefixWord, tailWord_373653, baseEnd_373653] using wordTrace_append hprefix tailTrace_373653
  have hstable : (prefixWord ++ tailWord_373653).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373653).length < 2 ^ (prefixWord ++ tailWord_373653).sum := by decide
  have hdescent : baseEnd_373653 < baseStart_373653 := by decide
  rcases family_descends (prefixWord ++ tailWord_373653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373718 : List Nat := [5, 2, 1, 1, 2, 1, 1, 3, 5]
def baseStart_373718 : Nat := 118140960795 + 373718 * 2 ^ 59
def prefixEnd_373718 : Nat := 4983230072969 + 3 ^ 40 * 373718 * 2
def baseEnd_373718 : Nat := 85287539216477360136137

theorem tailTrace_373718 : CollatzResearch.WordTrace tailWord_373718 prefixEnd_373718 85287539216477360136137 := by
  unfold tailWord_373718
  simp only [CollatzResearch.WordTrace]
  refine ⟨851913453755686674879113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9087076840060657865377205 851913453755686674879113)
  ·
    refine ⟨638935090316765006159335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 851913453755686674879113 638935090316765006159335)
    ·
      refine ⟨958402635475147509239003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 638935090316765006159335 958402635475147509239003)
      ·
        refine ⟨1437603953212721263858505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 958402635475147509239003 1437603953212721263858505)
        ·
          refine ⟨1078202964909540947893879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1437603953212721263858505 1078202964909540947893879)
          ·
            refine ⟨1617304447364311421840819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1078202964909540947893879 1617304447364311421840819)
            ·
              refine ⟨2425956671046467132761229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1617304447364311421840819 2425956671046467132761229)
              ·
                refine ⟨909733751642425174785461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2425956671046467132761229 909733751642425174785461)
                ·
                  refine ⟨85287539216477360136137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 909733751642425174785461 85287539216477360136137)
                  ·
                    rfl

theorem cell21_373718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_373718 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_373718 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_373718 prefixEnd_373718 := by exact prefixLift 373718
  have htrace : WordTrace (prefixWord ++ tailWord_373718) baseStart_373718 baseEnd_373718 := by
    simpa [prefixWord, tailWord_373718, baseEnd_373718] using wordTrace_append hprefix tailTrace_373718
  have hstable : (prefixWord ++ tailWord_373718).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373718).length < 2 ^ (prefixWord ++ tailWord_373718).sum := by decide
  have hdescent : baseEnd_373718 < baseStart_373718 := by decide
  rcases family_descends (prefixWord ++ tailWord_373718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373729 : List Nat := [1, 2, 3, 1, 2, 1, 1, 10]
def baseStart_373729 : Nat := 118140960795 + 373729 * 2 ^ 59
def prefixEnd_373729 : Nat := 4983230072969 + 3 ^ 40 * 373729 * 2
def baseEnd_373729 : Nat := 28430016522114595150927

theorem tailTrace_373729 : CollatzResearch.WordTrace tailWord_373729 prefixEnd_373729 28430016522114595150927 := by
  unfold tailWord_373729
  simp only [CollatzResearch.WordTrace]
  refine ⟨13631016463051135676716241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9087344308700757117810827 13631016463051135676716241)
  ·
    refine ⟨10223262347288351757537181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13631016463051135676716241 10223262347288351757537181)
    ·
      refine ⟨3833723380233131909076443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10223262347288351757537181 3833723380233131909076443)
      ·
        refine ⟨5750585070349697863614665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3833723380233131909076443 5750585070349697863614665)
        ·
          refine ⟨4312938802762273397710999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5750585070349697863614665 4312938802762273397710999)
          ·
            refine ⟨6469408204143410096566499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4312938802762273397710999 6469408204143410096566499)
            ·
              refine ⟨9704112306215115144849749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6469408204143410096566499 9704112306215115144849749)
              ·
                refine ⟨28430016522114595150927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 9704112306215115144849749 28430016522114595150927)
                ·
                  rfl

theorem cell21_373729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 10].length) (baseStart_373729 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_373729 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_373729 prefixEnd_373729 := by exact prefixLift 373729
  have htrace : WordTrace (prefixWord ++ tailWord_373729) baseStart_373729 baseEnd_373729 := by
    simpa [prefixWord, tailWord_373729, baseEnd_373729] using wordTrace_append hprefix tailTrace_373729
  have hstable : (prefixWord ++ tailWord_373729).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373729).length < 2 ^ (prefixWord ++ tailWord_373729).sum := by decide
  have hdescent : baseEnd_373729 < baseStart_373729 := by decide
  rcases family_descends (prefixWord ++ tailWord_373729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373777 : List Nat := [1, 2, 2, 1, 1, 2, 1, 8, 3]
def baseStart_373777 : Nat := 118140960795 + 373777 * 2 ^ 59
def prefixEnd_373777 : Nat := 4983230072969 + 3 ^ 40 * 373777 * 2
def baseEnd_373777 : Nat := 85301003820306368652683

theorem tailTrace_373777 : CollatzResearch.WordTrace tailWord_373777 prefixEnd_373777 85301003820306368652683 := by
  unfold tailWord_373777
  simp only [CollatzResearch.WordTrace]
  refine ⟨13632767166877239874463585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9088511444584826582975723 13632767166877239874463585)
  ·
    refine ⟨10224575375157929905847689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13632767166877239874463585 10224575375157929905847689)
    ·
      refine ⟨7668431531368447429385767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10224575375157929905847689 7668431531368447429385767)
      ·
        refine ⟨11502647297052671144078651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7668431531368447429385767 11502647297052671144078651)
        ·
          refine ⟨17253970945579006716117977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11502647297052671144078651 17253970945579006716117977)
          ·
            refine ⟨12940478209184255037088483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17253970945579006716117977 12940478209184255037088483)
            ·
              refine ⟨19410717313776382555632725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12940478209184255037088483 19410717313776382555632725)
              ·
                refine ⟨227469343520816983073821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 19410717313776382555632725 227469343520816983073821)
                ·
                  refine ⟨85301003820306368652683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 227469343520816983073821 85301003820306368652683)
                  ·
                    rfl

theorem cell21_373777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 8, 3].length) (baseStart_373777 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_373777 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_373777 prefixEnd_373777 := by exact prefixLift 373777
  have htrace : WordTrace (prefixWord ++ tailWord_373777) baseStart_373777 baseEnd_373777 := by
    simpa [prefixWord, tailWord_373777, baseEnd_373777] using wordTrace_append hprefix tailTrace_373777
  have hstable : (prefixWord ++ tailWord_373777).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373777).length < 2 ^ (prefixWord ++ tailWord_373777).sum := by decide
  have hdescent : baseEnd_373777 < baseStart_373777 := by decide
  rcases family_descends (prefixWord ++ tailWord_373777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373822 : List Nat := [4, 2, 1, 3, 1, 10]
def baseStart_373822 : Nat := 118140960795 + 373822 * 2 ^ 59
def prefixEnd_373822 : Nat := 4983230072969 + 3 ^ 40 * 373822 * 2
def baseEnd_373822 : Nat := 3159676793829492237133

theorem tailTrace_373822 : CollatzResearch.WordTrace tailWord_373822 prefixEnd_373822 3159676793829492237133 := by
  unfold tailWord_373822
  simp only [CollatzResearch.WordTrace]
  refine ⟨1704301056464276569981465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9089605634476141706567813 1704301056464276569981465)
  ·
    refine ⟨1278225792348207427486099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1704301056464276569981465 1278225792348207427486099)
    ·
      refine ⟨1917338688522311141229149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1278225792348207427486099 1917338688522311141229149)
      ·
        refine ⟨719002008195866677960931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1917338688522311141229149 719002008195866677960931)
        ·
          refine ⟨1078503012293800016941397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 719002008195866677960931 1078503012293800016941397)
          ·
            refine ⟨3159676793829492237133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1078503012293800016941397 3159676793829492237133)
            ·
              rfl

theorem cell21_373822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 10].length) (baseStart_373822 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_373822 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_373822 prefixEnd_373822 := by exact prefixLift 373822
  have htrace : WordTrace (prefixWord ++ tailWord_373822) baseStart_373822 baseEnd_373822 := by
    simpa [prefixWord, tailWord_373822, baseEnd_373822] using wordTrace_append hprefix tailTrace_373822
  have hstable : (prefixWord ++ tailWord_373822).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373822).length < 2 ^ (prefixWord ++ tailWord_373822).sum := by decide
  have hdescent : baseEnd_373822 < baseStart_373822 := by decide
  rcases family_descends (prefixWord ++ tailWord_373822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373825 : List Nat := [1, 2, 5, 1, 3, 1, 2, 2, 4]
def baseStart_373825 : Nat := 118140960795 + 373825 * 2 ^ 59
def prefixEnd_373825 : Nat := 4983230072969 + 3 ^ 40 * 373825 * 2
def baseEnd_373825 : Nat := 85311958074268951852585

theorem tailTrace_373825 : CollatzResearch.WordTrace tailWord_373825 prefixEnd_373825 85311958074268951852585 := by
  unfold tailWord_373825
  simp only [CollatzResearch.WordTrace]
  refine ⟨13634517870703344072210929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9089678580468896048140619 13634517870703344072210929)
  ·
    refine ⟨10225888403027508054158197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13634517870703344072210929 10225888403027508054158197)
    ·
      refine ⟨958677037783828880077331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10225888403027508054158197 958677037783828880077331)
      ·
        refine ⟨1438015556675743320115997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 958677037783828880077331 1438015556675743320115997)
        ·
          refine ⟨539255833753403745043499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1438015556675743320115997 539255833753403745043499)
          ·
            refine ⟨808883750630105617565249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 539255833753403745043499 808883750630105617565249)
            ·
              refine ⟨606662812972579213173937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 808883750630105617565249 606662812972579213173937)
              ·
                refine ⟨454997109729434409880453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 606662812972579213173937 454997109729434409880453)
                ·
                  refine ⟨85311958074268951852585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 454997109729434409880453 85311958074268951852585)
                  ·
                    rfl

theorem cell21_373825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 2, 4].length) (baseStart_373825 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_373825 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_373825 prefixEnd_373825 := by exact prefixLift 373825
  have htrace : WordTrace (prefixWord ++ tailWord_373825) baseStart_373825 baseEnd_373825 := by
    simpa [prefixWord, tailWord_373825, baseEnd_373825] using wordTrace_append hprefix tailTrace_373825
  have hstable : (prefixWord ++ tailWord_373825).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373825).length < 2 ^ (prefixWord ++ tailWord_373825).sum := by decide
  have hdescent : baseEnd_373825 < baseStart_373825 := by decide
  rcases family_descends (prefixWord ++ tailWord_373825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373836 : List Nat := [2, 2, 1, 3, 1, 1, 1, 5, 5]
def baseStart_373836 : Nat := 118140960795 + 373836 * 2 ^ 59
def prefixEnd_373836 : Nat := 4983230072969 + 3 ^ 40 * 373836 * 2
def baseEnd_373836 : Nat := 85314468424135377169229

theorem tailTrace_373836 : CollatzResearch.WordTrace tailWord_373836 prefixEnd_373836 85314468424135377169229 := by
  unfold tailWord_373836
  simp only [CollatzResearch.WordTrace]
  refine ⟨6817459536831746475430681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9089946049108995300574241 6817459536831746475430681)
  ·
    refine ⟨5113094652623809856573011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6817459536831746475430681 5113094652623809856573011)
    ·
      refine ⟨7669641978935714784859517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5113094652623809856573011 7669641978935714784859517)
      ·
        refine ⟨2876115742100893044322319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7669641978935714784859517 2876115742100893044322319)
        ·
          refine ⟨4314173613151339566483479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2876115742100893044322319 4314173613151339566483479)
          ·
            refine ⟨6471260419727009349725219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4314173613151339566483479 6471260419727009349725219)
            ·
              refine ⟨9706890629590514024587829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6471260419727009349725219 9706890629590514024587829)
              ·
                refine ⟨910020996524110689805109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9706890629590514024587829 910020996524110689805109)
                ·
                  refine ⟨85314468424135377169229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 910020996524110689805109 85314468424135377169229)
                  ·
                    rfl

theorem cell21_373836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5, 5].length) (baseStart_373836 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_373836 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_373836 prefixEnd_373836 := by exact prefixLift 373836
  have htrace : WordTrace (prefixWord ++ tailWord_373836) baseStart_373836 baseEnd_373836 := by
    simpa [prefixWord, tailWord_373836, baseEnd_373836] using wordTrace_append hprefix tailTrace_373836
  have hstable : (prefixWord ++ tailWord_373836).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373836).length < 2 ^ (prefixWord ++ tailWord_373836).sum := by decide
  have hdescent : baseEnd_373836 < baseStart_373836 := by decide
  rcases family_descends (prefixWord ++ tailWord_373836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373870 : List Nat := [4, 1, 2, 2, 1, 2, 1, 5, 3]
def baseStart_373870 : Nat := 118140960795 + 373870 * 2 ^ 59
def prefixEnd_373870 : Nat := 4983230072969 + 3 ^ 40 * 373870 * 2
def baseEnd_373870 : Nat := 85322227687358873602493

theorem tailTrace_373870 : CollatzResearch.WordTrace tailWord_373870 prefixEnd_373870 85322227687358873602493 := by
  unfold tailWord_373870
  simp only [CollatzResearch.WordTrace]
  refine ⟨1704519894442539594699883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9090772770360211171732709 1704519894442539594699883)
  ·
    refine ⟨2556779841663809392049825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1704519894442539594699883 2556779841663809392049825)
    ·
      refine ⟨1917584881247857044037369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2556779841663809392049825 1917584881247857044037369)
      ·
        refine ⟨1438188660935892783028027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1917584881247857044037369 1438188660935892783028027)
        ·
          refine ⟨2157282991403839174542041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1438188660935892783028027 2157282991403839174542041)
          ·
            refine ⟨1617962243552879380906531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2157282991403839174542041 1617962243552879380906531)
            ·
              refine ⟨2426943365329319071359797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1617962243552879380906531 2426943365329319071359797)
              ·
                refine ⟨227525940499623662939981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2426943365329319071359797 227525940499623662939981)
                ·
                  refine ⟨85322227687358873602493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 227525940499623662939981 85322227687358873602493)
                  ·
                    rfl

theorem cell21_373870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 5, 3].length) (baseStart_373870 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_373870 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_373870 prefixEnd_373870 := by exact prefixLift 373870
  have htrace : WordTrace (prefixWord ++ tailWord_373870) baseStart_373870 baseEnd_373870 := by
    simpa [prefixWord, tailWord_373870, baseEnd_373870] using wordTrace_append hprefix tailTrace_373870
  have hstable : (prefixWord ++ tailWord_373870).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373870).length < 2 ^ (prefixWord ++ tailWord_373870).sum := by decide
  have hdescent : baseEnd_373870 < baseStart_373870 := by decide
  rcases family_descends (prefixWord ++ tailWord_373870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373943 : List Nat := [1, 1, 3, 1, 4, 1, 2, 4, 4]
def baseStart_373943 : Nat := 118140960795 + 373943 * 2 ^ 59
def prefixEnd_373943 : Nat := 4983230072969 + 3 ^ 40 * 373943 * 2
def baseEnd_373943 : Nat := 85338887281926968885677

theorem tailTrace_373943 : CollatzResearch.WordTrace tailWord_373943 prefixEnd_373943 85338887281926968885677 := by
  unfold tailWord_373943
  simp only [CollatzResearch.WordTrace]
  refine ⟨13638821684275850225006483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9092547789517233483337655 13638821684275850225006483)
  ·
    refine ⟨20458232526413775337509725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13638821684275850225006483 20458232526413775337509725)
    ·
      refine ⟨7671837197405165751566147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20458232526413775337509725 7671837197405165751566147)
      ·
        refine ⟨11507755796107748627349221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7671837197405165751566147 11507755796107748627349221)
        ·
          refine ⟨2157704211770202867627979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11507755796107748627349221 2157704211770202867627979)
          ·
            refine ⟨3236556317655304301441969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2157704211770202867627979 3236556317655304301441969)
            ·
              refine ⟨2427417238241478226081477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3236556317655304301441969 2427417238241478226081477)
              ·
                refine ⟨455140732170277167390277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2427417238241478226081477 455140732170277167390277)
                ·
                  refine ⟨85338887281926968885677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 455140732170277167390277 85338887281926968885677)
                  ·
                    rfl

theorem cell21_373943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 4, 4].length) (baseStart_373943 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_373943 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_373943 prefixEnd_373943 := by exact prefixLift 373943
  have htrace : WordTrace (prefixWord ++ tailWord_373943) baseStart_373943 baseEnd_373943 := by
    simpa [prefixWord, tailWord_373943, baseEnd_373943] using wordTrace_append hprefix tailTrace_373943
  have hstable : (prefixWord ++ tailWord_373943).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373943).length < 2 ^ (prefixWord ++ tailWord_373943).sum := by decide
  have hdescent : baseEnd_373943 < baseStart_373943 := by decide
  rcases family_descends (prefixWord ++ tailWord_373943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373960 : List Nat := [2, 1, 3, 1, 2, 1, 6, 1, 4]
def baseStart_373960 : Nat := 118140960795 + 373960 * 2 ^ 59
def prefixEnd_373960 : Nat := 4983230072969 + 3 ^ 40 * 373960 * 2
def baseEnd_373960 : Nat := 85342766913538717102309

theorem tailTrace_373960 : CollatzResearch.WordTrace tailWord_373960 prefixEnd_373960 85342766913538717102309 := by
  unfold tailWord_373960
  simp only [CollatzResearch.WordTrace]
  refine ⟨6819720862607131064187667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9092961150142841418916889 6819720862607131064187667)
  ·
    refine ⟨10229581293910696596281501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6819720862607131064187667 10229581293910696596281501)
    ·
      refine ⟨3836092985216511223605563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10229581293910696596281501 3836092985216511223605563)
      ·
        refine ⟨5754139477824766835408345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3836092985216511223605563 5754139477824766835408345)
        ·
          refine ⟨4315604608368575126556259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5754139477824766835408345 4315604608368575126556259)
          ·
            refine ⟨6473406912552862689834389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4315604608368575126556259 6473406912552862689834389)
            ·
              refine ⟨303440949025915438585987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6473406912552862689834389 303440949025915438585987)
              ·
                refine ⟨455161423538873157878981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 303440949025915438585987 455161423538873157878981)
                ·
                  refine ⟨85342766913538717102309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 455161423538873157878981 85342766913538717102309)
                  ·
                    rfl

theorem cell21_373960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6, 1, 4].length) (baseStart_373960 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_373960 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_373960 prefixEnd_373960 := by exact prefixLift 373960
  have htrace : WordTrace (prefixWord ++ tailWord_373960) baseStart_373960 baseEnd_373960 := by
    simpa [prefixWord, tailWord_373960, baseEnd_373960] using wordTrace_append hprefix tailTrace_373960
  have hstable : (prefixWord ++ tailWord_373960).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373960).length < 2 ^ (prefixWord ++ tailWord_373960).sum := by decide
  have hdescent : baseEnd_373960 < baseStart_373960 := by decide
  rcases family_descends (prefixWord ++ tailWord_373960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374019 : List Nat := [1, 1, 1, 3, 2, 4, 2, 3, 4]
def baseStart_374019 : Nat := 118140960795 + 374019 * 2 ^ 59
def prefixEnd_374019 : Nat := 4983230072969 + 3 ^ 40 * 374019 * 2
def baseEnd_374019 : Nat := 85356231517367725618855

theorem tailTrace_374019 : CollatzResearch.WordTrace tailWord_374019 prefixEnd_374019 85356231517367725618855 := by
  unfold tailWord_374019
  simp only [CollatzResearch.WordTrace]
  refine ⟨13641593632000515204773111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9094395754667010136515407 13641593632000515204773111)
  ·
    refine ⟨20462390448000772807159667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13641593632000515204773111 20462390448000772807159667)
    ·
      refine ⟨30693585672001159210739501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20462390448000772807159667 30693585672001159210739501)
      ·
        refine ⟨11510094627000434704027313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30693585672001159210739501 11510094627000434704027313)
        ·
          refine ⟨8632570970250326028020485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11510094627000434704027313 8632570970250326028020485)
          ·
            refine ⟨1618607056921936130253841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8632570970250326028020485 1618607056921936130253841)
            ·
              refine ⟨1213955292691452097690381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1618607056921936130253841 1213955292691452097690381)
              ·
                refine ⟨455233234759294536633893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1213955292691452097690381 455233234759294536633893)
                ·
                  refine ⟨85356231517367725618855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 455233234759294536633893 85356231517367725618855)
                  ·
                    rfl

theorem cell21_374019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 3, 4].length) (baseStart_374019 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_374019 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_374019 prefixEnd_374019 := by exact prefixLift 374019
  have htrace : WordTrace (prefixWord ++ tailWord_374019) baseStart_374019 baseEnd_374019 := by
    simpa [prefixWord, tailWord_374019, baseEnd_374019] using wordTrace_append hprefix tailTrace_374019
  have hstable : (prefixWord ++ tailWord_374019).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374019).length < 2 ^ (prefixWord ++ tailWord_374019).sum := by decide
  have hdescent : baseEnd_374019 < baseStart_374019 := by decide
  rcases family_descends (prefixWord ++ tailWord_374019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374050 : List Nat := [3, 3, 1, 1, 4, 1, 8]
def baseStart_374050 : Nat := 118140960795 + 374050 * 2 ^ 59
def prefixEnd_374050 : Nat := 4983230072969 + 3 ^ 40 * 374050 * 2
def baseEnd_374050 : Nat := 9484811793302062289125

theorem tailTrace_374050 : CollatzResearch.WordTrace tailWord_374050 prefixEnd_374050 9484811793302062289125 := by
  unfold tailWord_374050
  simp only [CollatzResearch.WordTrace]
  refine ⟨3410681073722051874787901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9095149529925471666101069 3410681073722051874787901)
  ·
    refine ⟨1279005402645769453045463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3410681073722051874787901 1279005402645769453045463)
    ·
      refine ⟨1918508103968654179568195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1279005402645769453045463 1918508103968654179568195)
      ·
        refine ⟨2877762155952981269352293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1918508103968654179568195 2877762155952981269352293)
        ·
          refine ⟨539580404241183988003555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2877762155952981269352293 539580404241183988003555)
          ·
            refine ⟨809370606361775982005333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 539580404241183988003555 809370606361775982005333)
            ·
              refine ⟨9484811793302062289125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 809370606361775982005333 9484811793302062289125)
              ·
                rfl

theorem cell21_374050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 8].length) (baseStart_374050 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_374050 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_374050 prefixEnd_374050 := by exact prefixLift 374050
  have htrace : WordTrace (prefixWord ++ tailWord_374050) baseStart_374050 baseEnd_374050 := by
    simpa [prefixWord, tailWord_374050, baseEnd_374050] using wordTrace_append hprefix tailTrace_374050
  have hstable : (prefixWord ++ tailWord_374050).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374050).length < 2 ^ (prefixWord ++ tailWord_374050).sum := by decide
  have hdescent : baseEnd_374050 < baseStart_374050 := by decide
  rcases family_descends (prefixWord ++ tailWord_374050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374064 : List Nat := [2, 1, 1, 1, 2, 2, 6, 1, 5]
def baseStart_374064 : Nat := 118140960795 + 374064 * 2 ^ 59
def prefixEnd_374064 : Nat := 4983230072969 + 3 ^ 40 * 374064 * 2
def baseEnd_374064 : Nat := 85366501130457647368763

theorem tailTrace_374064 : CollatzResearch.WordTrace tailWord_374064 prefixEnd_374064 85366501130457647368763 := by
  unfold tailWord_374064
  simp only [CollatzResearch.WordTrace]
  refine ⟨6821617458418743945080623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9095489944558325260107497 6821617458418743945080623)
  ·
    refine ⟨10232426187628115917620935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6821617458418743945080623 10232426187628115917620935)
    ·
      refine ⟨15348639281442173876431403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10232426187628115917620935 15348639281442173876431403)
      ·
        refine ⟨23022958922163260814647105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15348639281442173876431403 23022958922163260814647105)
        ·
          refine ⟨17267219191622445610985329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23022958922163260814647105 17267219191622445610985329)
          ·
            refine ⟨12950414393716834208238997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17267219191622445610985329 12950414393716834208238997)
            ·
              refine ⟨607050674705476603511203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12950414393716834208238997 607050674705476603511203)
              ·
                refine ⟨910576012058214905266805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 607050674705476603511203 910576012058214905266805)
                ·
                  refine ⟨85366501130457647368763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 910576012058214905266805 85366501130457647368763)
                  ·
                    rfl

theorem cell21_374064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 1, 5].length) (baseStart_374064 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_374064 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_374064 prefixEnd_374064 := by exact prefixLift 374064
  have htrace : WordTrace (prefixWord ++ tailWord_374064) baseStart_374064 baseEnd_374064 := by
    simpa [prefixWord, tailWord_374064, baseEnd_374064] using wordTrace_append hprefix tailTrace_374064
  have hstable : (prefixWord ++ tailWord_374064).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374064).length < 2 ^ (prefixWord ++ tailWord_374064).sum := by decide
  have hdescent : baseEnd_374064 < baseStart_374064 := by decide
  rcases family_descends (prefixWord ++ tailWord_374064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374081 : List Nat := [1, 2, 5, 2, 1, 1, 2, 2, 5]
def baseStart_374081 : Nat := 118140960795 + 374081 * 2 ^ 59
def prefixEnd_374081 : Nat := 4983230072969 + 3 ^ 40 * 374081 * 2
def baseEnd_374081 : Nat := 85370380762069395585395

theorem tailTrace_374081 : CollatzResearch.WordTrace tailWord_374081 prefixEnd_374081 85370380762069395585395 := by
  unfold tailWord_374081
  simp only [CollatzResearch.WordTrace]
  refine ⟨13643854957775899793530097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9095903305183933195686731 13643854957775899793530097)
  ·
    refine ⟨10232891218331924845147573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13643854957775899793530097 10232891218331924845147573)
    ·
      refine ⟨959333551718617954232585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10232891218331924845147573 959333551718617954232585)
      ·
        refine ⟨719500163788963465674439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 959333551718617954232585 719500163788963465674439)
        ·
          refine ⟨1079250245683445198511659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 719500163788963465674439 1079250245683445198511659)
          ·
            refine ⟨1618875368525167797767489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1079250245683445198511659 1618875368525167797767489)
            ·
              refine ⟨1214156526393875848325617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1618875368525167797767489 1214156526393875848325617)
              ·
                refine ⟨910617394795406886244213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1214156526393875848325617 910617394795406886244213)
                ·
                  refine ⟨85370380762069395585395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 910617394795406886244213 85370380762069395585395)
                  ·
                    rfl

theorem cell21_374081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 2, 5].length) (baseStart_374081 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_374081 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_374081 prefixEnd_374081 := by exact prefixLift 374081
  have htrace : WordTrace (prefixWord ++ tailWord_374081) baseStart_374081 baseEnd_374081 := by
    simpa [prefixWord, tailWord_374081, baseEnd_374081] using wordTrace_append hprefix tailTrace_374081
  have hstable : (prefixWord ++ tailWord_374081).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374081).length < 2 ^ (prefixWord ++ tailWord_374081).sum := by decide
  have hdescent : baseEnd_374081 < baseStart_374081 := by decide
  rcases family_descends (prefixWord ++ tailWord_374081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374084 : List Nat := [2, 3, 4, 1, 1, 3, 2, 5]
def baseStart_374084 : Nat := 118140960795 + 374084 * 2 ^ 59
def prefixEnd_374084 : Nat := 4983230072969 + 3 ^ 40 * 374084 * 2
def baseEnd_374084 : Nat := 28457021800980685678463

theorem tailTrace_374084 : CollatzResearch.WordTrace tailWord_374084 prefixEnd_374084 28457021800980685678463 := by
  unfold tailWord_374084
  simp only [CollatzResearch.WordTrace]
  refine ⟨6821982188382515652944653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9095976251176687537259537 6821982188382515652944653)
  ·
    refine ⟨2558243320643443369854245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6821982188382515652944653 2558243320643443369854245)
    ·
      refine ⟨479670622620645631847671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2558243320643443369854245 479670622620645631847671)
      ·
        refine ⟨719505933930968447771507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 479670622620645631847671 719505933930968447771507)
        ·
          refine ⟨1079258900896452671657261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 719505933930968447771507 1079258900896452671657261)
          ·
            refine ⟨404722087836169751871473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1079258900896452671657261 404722087836169751871473)
            ·
              refine ⟨303541565877127313903605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 404722087836169751871473 303541565877127313903605)
              ·
                refine ⟨28457021800980685678463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 303541565877127313903605 28457021800980685678463)
                ·
                  rfl

theorem cell21_374084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2, 5].length) (baseStart_374084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_374084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_374084 prefixEnd_374084 := by exact prefixLift 374084
  have htrace : WordTrace (prefixWord ++ tailWord_374084) baseStart_374084 baseEnd_374084 := by
    simpa [prefixWord, tailWord_374084, baseEnd_374084] using wordTrace_append hprefix tailTrace_374084
  have hstable : (prefixWord ++ tailWord_374084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374084).length < 2 ^ (prefixWord ++ tailWord_374084).sum := by decide
  have hdescent : baseEnd_374084 < baseStart_374084 := by decide
  rcases family_descends (prefixWord ++ tailWord_374084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374233 : List Nat := [1, 2, 1, 2, 4, 2, 2, 4, 3]
def baseStart_374233 : Nat := 118140960795 + 374233 * 2 ^ 59
def prefixEnd_374233 : Nat := 4983230072969 + 3 ^ 40 * 374233 * 2
def baseEnd_374233 : Nat := 85405069232950909051751

theorem tailTrace_374233 : CollatzResearch.WordTrace tailWord_374233 prefixEnd_374233 85405069232950909051751 := by
  unfold tailWord_374233
  simp only [CollatzResearch.WordTrace]
  refine ⟨13649398853225229753063353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9099599235483486502042235 13649398853225229753063353)
  ·
    refine ⟨10237049139918922314797515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13649398853225229753063353 10237049139918922314797515)
    ·
      refine ⟨15355573709878383472196273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10237049139918922314797515 15355573709878383472196273)
      ·
        refine ⟨11516680282408787604147205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15355573709878383472196273 11516680282408787604147205)
        ·
          refine ⟨2159377552951647675777601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11516680282408787604147205 2159377552951647675777601)
          ·
            refine ⟨1619533164713735756833201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2159377552951647675777601 1619533164713735756833201)
            ·
              refine ⟨1214649873535301817624901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1619533164713735756833201 1214649873535301817624901)
              ·
                refine ⟨227746851287869090804669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1214649873535301817624901 227746851287869090804669)
                ·
                  refine ⟨85405069232950909051751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 227746851287869090804669 85405069232950909051751)
                  ·
                    rfl

theorem cell21_374233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 4, 3].length) (baseStart_374233 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_374233 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_374233 prefixEnd_374233 := by exact prefixLift 374233
  have htrace : WordTrace (prefixWord ++ tailWord_374233) baseStart_374233 baseEnd_374233 := by
    simpa [prefixWord, tailWord_374233, baseEnd_374233] using wordTrace_append hprefix tailTrace_374233
  have hstable : (prefixWord ++ tailWord_374233).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374233).length < 2 ^ (prefixWord ++ tailWord_374233).sum := by decide
  have hdescent : baseEnd_374233 < baseStart_374233 := by decide
  rcases family_descends (prefixWord ++ tailWord_374233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374343 : List Nat := [1, 1, 4, 1, 5, 2, 2, 2, 3]
def baseStart_374343 : Nat := 118140960795 + 374343 * 2 ^ 59
def prefixEnd_374343 : Nat := 4983230072969 + 3 ^ 40 * 374343 * 2
def baseEnd_374343 : Nat := 85430172731615162218193

theorem tailTrace_374343 : CollatzResearch.WordTrace tailWord_374343 prefixEnd_374343 85430172731615162218193 := by
  unfold tailWord_374343
  simp only [CollatzResearch.WordTrace]
  refine ⟨13653410882826718539567683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9102273921884479026378455 13653410882826718539567683)
  ·
    refine ⟨20480116324240077809351525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13653410882826718539567683 20480116324240077809351525)
    ·
      refine ⟨3840021810795014589253411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20480116324240077809351525 3840021810795014589253411)
      ·
        refine ⟨5760032716192521883880117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3840021810795014589253411 5760032716192521883880117)
        ·
          refine ⟨540003067143048926613761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5760032716192521883880117 540003067143048926613761)
          ·
            refine ⟨405002300357286694960321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 540003067143048926613761 405002300357286694960321)
            ·
              refine ⟨303751725267965021220241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 405002300357286694960321 303751725267965021220241)
              ·
                refine ⟨227813793950973765915181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 303751725267965021220241 227813793950973765915181)
                ·
                  refine ⟨85430172731615162218193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 227813793950973765915181 85430172731615162218193)
                  ·
                    rfl

theorem cell21_374343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2, 2, 3].length) (baseStart_374343 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_374343 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_374343 prefixEnd_374343 := by exact prefixLift 374343
  have htrace : WordTrace (prefixWord ++ tailWord_374343) baseStart_374343 baseEnd_374343 := by
    simpa [prefixWord, tailWord_374343, baseEnd_374343] using wordTrace_append hprefix tailTrace_374343
  have hstable : (prefixWord ++ tailWord_374343).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374343).length < 2 ^ (prefixWord ++ tailWord_374343).sum := by decide
  have hdescent : baseEnd_374343 < baseStart_374343 := by decide
  rcases family_descends (prefixWord ++ tailWord_374343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374351 : List Nat := [1, 1, 2, 1, 1, 2, 3, 5, 5]
def baseStart_374351 : Nat := 118140960795 + 374351 * 2 ^ 59
def prefixEnd_374351 : Nat := 4983230072969 + 3 ^ 40 * 374351 * 2
def baseEnd_374351 : Nat := 85431998440608926084843

theorem tailTrace_374351 : CollatzResearch.WordTrace tailWord_374351 prefixEnd_374351 85431998440608926084843 := by
  unfold tailWord_374351
  simp only [CollatzResearch.WordTrace]
  refine ⟨13653702666797735905858907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9102468444531823937239271 13653702666797735905858907)
  ·
    refine ⟨20480554000196603858788361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13653702666797735905858907 20480554000196603858788361)
    ·
      refine ⟨15360415500147452894091271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20480554000196603858788361 15360415500147452894091271)
      ·
        refine ⟨23040623250221179341136907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15360415500147452894091271 23040623250221179341136907)
        ·
          refine ⟨34560934875331769011705361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23040623250221179341136907 34560934875331769011705361)
          ·
            refine ⟨25920701156498826758779021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34560934875331769011705361 25920701156498826758779021)
            ·
              refine ⟨9720262933687060034542133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25920701156498826758779021 9720262933687060034542133)
              ·
                refine ⟨911274650033161878238325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9720262933687060034542133 911274650033161878238325)
                ·
                  refine ⟨85431998440608926084843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 911274650033161878238325 85431998440608926084843)
                  ·
                    rfl

theorem cell21_374351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5, 5].length) (baseStart_374351 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_374351 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_374351 prefixEnd_374351 := by exact prefixLift 374351
  have htrace : WordTrace (prefixWord ++ tailWord_374351) baseStart_374351 baseEnd_374351 := by
    simpa [prefixWord, tailWord_374351, baseEnd_374351] using wordTrace_append hprefix tailTrace_374351
  have hstable : (prefixWord ++ tailWord_374351).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374351).length < 2 ^ (prefixWord ++ tailWord_374351).sum := by decide
  have hdescent : baseEnd_374351 < baseStart_374351 := by decide
  rcases family_descends (prefixWord ++ tailWord_374351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374354 : List Nat := [3, 2, 2, 1, 2, 4, 1, 6]
def baseStart_374354 : Nat := 118140960795 + 374354 * 2 ^ 59
def prefixEnd_374354 : Nat := 4983230072969 + 3 ^ 40 * 374354 * 2
def baseEnd_374354 : Nat := 28477561027160529178279

theorem tailTrace_374354 : CollatzResearch.WordTrace tailWord_374354 prefixEnd_374354 28477561027160529178279 := by
  unfold tailWord_374354
  simp only [CollatzResearch.WordTrace]
  refine ⟨3413453021446716854554529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9102541390524578278812077 3413453021446716854554529)
  ·
    refine ⟨2560089766085037640915897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3413453021446716854554529 2560089766085037640915897)
    ·
      refine ⟨1920067324563778230686923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2560089766085037640915897 1920067324563778230686923)
      ·
        refine ⟨2880100986845667346030385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1920067324563778230686923 2880100986845667346030385)
        ·
          refine ⟨2160075740134250509522789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2880100986845667346030385 2160075740134250509522789)
          ·
            refine ⟨405014201275171970535523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2160075740134250509522789 405014201275171970535523)
            ·
              refine ⟨607521301912757955803285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 405014201275171970535523 607521301912757955803285)
              ·
                refine ⟨28477561027160529178279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 607521301912757955803285 28477561027160529178279)
                ·
                  rfl

theorem cell21_374354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 6].length) (baseStart_374354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_374354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_374354 prefixEnd_374354 := by exact prefixLift 374354
  have htrace : WordTrace (prefixWord ++ tailWord_374354) baseStart_374354 baseEnd_374354 := by
    simpa [prefixWord, tailWord_374354, baseEnd_374354] using wordTrace_append hprefix tailTrace_374354
  have hstable : (prefixWord ++ tailWord_374354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374354).length < 2 ^ (prefixWord ++ tailWord_374354).sum := by decide
  have hdescent : baseEnd_374354 < baseStart_374354 := by decide
  rcases family_descends (prefixWord ++ tailWord_374354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374430 : List Nat := [4, 3, 1, 1, 1, 3, 1, 7]
def baseStart_374430 : Nat := 118140960795 + 374430 * 2 ^ 59
def prefixEnd_374430 : Nat := 4983230072969 + 3 ^ 40 * 374430 * 2
def baseEnd_374430 : Nat := 28483342438974114756005

theorem tailTrace_374430 : CollatzResearch.WordTrace tailWord_374430 prefixEnd_374430 28483342438974114756005 := by
  unfold tailWord_374430
  simp only [CollatzResearch.WordTrace]
  refine ⟨1707073004188941549748093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9104389355674354931989829 1707073004188941549748093)
  ·
    refine ⟨640152376570853081155535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1707073004188941549748093 640152376570853081155535)
    ·
      refine ⟨960228564856279621733303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 640152376570853081155535 960228564856279621733303)
      ·
        refine ⟨1440342847284419432599955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 960228564856279621733303 1440342847284419432599955)
        ·
          refine ⟨2160514270926629148899933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1440342847284419432599955 2160514270926629148899933)
          ·
            refine ⟨810192851597485930837475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2160514270926629148899933 810192851597485930837475)
            ·
              refine ⟨1215289277396228896256213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 810192851597485930837475 1215289277396228896256213)
              ·
                refine ⟨28483342438974114756005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1215289277396228896256213 28483342438974114756005)
                ·
                  rfl

theorem cell21_374430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 7].length) (baseStart_374430 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_374430 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_374430 prefixEnd_374430 := by exact prefixLift 374430
  have htrace : WordTrace (prefixWord ++ tailWord_374430) baseStart_374430 baseEnd_374430 := by
    simpa [prefixWord, tailWord_374430, baseEnd_374430] using wordTrace_append hprefix tailTrace_374430
  have hstable : (prefixWord ++ tailWord_374430).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374430).length < 2 ^ (prefixWord ++ tailWord_374430).sum := by decide
  have hdescent : baseEnd_374430 < baseStart_374430 := by decide
  rcases family_descends (prefixWord ++ tailWord_374430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374458 : List Nat := [3, 1, 1, 1, 2, 4, 2, 1, 6]
def baseStart_374458 : Nat := 118140960795 + 374458 * 2 ^ 59
def prefixEnd_374458 : Nat := 4983230072969 + 3 ^ 40 * 374458 * 2
def baseEnd_374458 : Nat := 85456417298400517801291

theorem tailTrace_374458 : CollatzResearch.WordTrace tailWord_374458 prefixEnd_374458 85456417298400517801291 := by
  unfold tailWord_374458
  simp only [CollatzResearch.WordTrace]
  refine ⟨3414401319352523295001007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9105070184940062120002685 3414401319352523295001007)
  ·
    refine ⟨5121601979028784942501511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3414401319352523295001007 5121601979028784942501511)
    ·
      refine ⟨7682402968543177413752267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5121601979028784942501511 7682402968543177413752267)
      ·
        refine ⟨11523604452814766120628401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7682402968543177413752267 11523604452814766120628401)
        ·
          refine ⟨8642703339611074590471301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11523604452814766120628401 8642703339611074590471301)
          ·
            refine ⟨1620506876177076485713369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8642703339611074590471301 1620506876177076485713369)
            ·
              refine ⟨1215380157132807364285027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1620506876177076485713369 1215380157132807364285027)
              ·
                refine ⟨1823070235699211046427541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1215380157132807364285027 1823070235699211046427541)
                ·
                  refine ⟨85456417298400517801291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1823070235699211046427541 85456417298400517801291)
                  ·
                    rfl

theorem cell21_374458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 6].length) (baseStart_374458 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_374458 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_374458 prefixEnd_374458 := by exact prefixLift 374458
  have htrace : WordTrace (prefixWord ++ tailWord_374458) baseStart_374458 baseEnd_374458 := by
    simpa [prefixWord, tailWord_374458, baseEnd_374458] using wordTrace_append hprefix tailTrace_374458
  have hstable : (prefixWord ++ tailWord_374458).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374458).length < 2 ^ (prefixWord ++ tailWord_374458).sum := by decide
  have hdescent : baseEnd_374458 < baseStart_374458 := by decide
  rcases family_descends (prefixWord ++ tailWord_374458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374568 : List Nat := [2, 1, 5, 1, 1, 4, 1, 2, 4]
def baseStart_374568 : Nat := 118140960795 + 374568 * 2 ^ 59
def prefixEnd_374568 : Nat := 4983230072969 + 3 ^ 40 * 374568 * 2
def baseEnd_374568 : Nat := 85481520797064770967733

theorem tailTrace_374568 : CollatzResearch.WordTrace tailWord_374568 prefixEnd_374568 85481520797064770967733 := by
  unfold tailWord_374568
  simp only [CollatzResearch.WordTrace]
  refine ⟨6830808653505790983254179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9107744871341054644338905 6830808653505790983254179)
  ·
    refine ⟨10246212980258686474881269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6830808653505790983254179 10246212980258686474881269)
    ·
      refine ⟨960582466899251857020119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10246212980258686474881269 960582466899251857020119)
      ·
        refine ⟨1440873700348877785530179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 960582466899251857020119 1440873700348877785530179)
        ·
          refine ⟨2161310550523316678295269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1440873700348877785530179 2161310550523316678295269)
          ·
            refine ⟨405245728223121877180363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2161310550523316678295269 405245728223121877180363)
            ·
              refine ⟨607868592334682815770545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 405245728223121877180363 607868592334682815770545)
              ·
                refine ⟨455901444251012111827909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 607868592334682815770545 455901444251012111827909)
                ·
                  refine ⟨85481520797064770967733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 455901444251012111827909 85481520797064770967733)
                  ·
                    rfl

theorem cell21_374568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 2, 4].length) (baseStart_374568 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_374568 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_374568 prefixEnd_374568 := by exact prefixLift 374568
  have htrace : WordTrace (prefixWord ++ tailWord_374568) baseStart_374568 baseEnd_374568 := by
    simpa [prefixWord, tailWord_374568, baseEnd_374568] using wordTrace_append hprefix tailTrace_374568
  have hstable : (prefixWord ++ tailWord_374568).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374568).length < 2 ^ (prefixWord ++ tailWord_374568).sum := by decide
  have hdescent : baseEnd_374568 < baseStart_374568 := by decide
  rcases family_descends (prefixWord ++ tailWord_374568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374585 : List Nat := [1, 2, 1, 7, 1, 1, 3, 1, 4]
def baseStart_374585 : Nat := 118140960795 + 374585 * 2 ^ 59
def prefixEnd_374585 : Nat := 4983230072969 + 3 ^ 40 * 374585 * 2
def baseEnd_374585 : Nat := 85485400428676519184365

theorem tailTrace_374585 : CollatzResearch.WordTrace tailWord_374585 prefixEnd_374585 85485400428676519184365 := by
  unfold tailWord_374585
  simp only [CollatzResearch.WordTrace]
  refine ⟨13662237347949993869877209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9108158231966662579918139 13662237347949993869877209)
  ·
    refine ⟨10246678010962495402407907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13662237347949993869877209 10246678010962495402407907)
    ·
      refine ⟨15370017016443743103611861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10246678010962495402407907 15370017016443743103611861)
      ·
        refine ⟨360234773822900228990903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 15370017016443743103611861 360234773822900228990903)
        ·
          refine ⟨540352160734350343486355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360234773822900228990903 540352160734350343486355)
          ·
            refine ⟨810528241101525515229533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 540352160734350343486355 810528241101525515229533)
            ·
              refine ⟨303948090413072068211075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 810528241101525515229533 303948090413072068211075)
              ·
                refine ⟨455922135619608102316613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 303948090413072068211075 455922135619608102316613)
                ·
                  refine ⟨85485400428676519184365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 455922135619608102316613 85485400428676519184365)
                  ·
                    rfl

theorem cell21_374585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3, 1, 4].length) (baseStart_374585 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_374585 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_374585 prefixEnd_374585 := by exact prefixLift 374585
  have htrace : WordTrace (prefixWord ++ tailWord_374585) baseStart_374585 baseEnd_374585 := by
    simpa [prefixWord, tailWord_374585, baseEnd_374585] using wordTrace_append hprefix tailTrace_374585
  have hstable : (prefixWord ++ tailWord_374585).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374585).length < 2 ^ (prefixWord ++ tailWord_374585).sum := by decide
  have hdescent : baseEnd_374585 < baseStart_374585 := by decide
  rcases family_descends (prefixWord ++ tailWord_374585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374610 : List Nat := [3, 2, 2, 1, 1, 3, 1, 2, 6]
def baseStart_374610 : Nat := 118140960795 + 374610 * 2 ^ 59
def prefixEnd_374610 : Nat := 4983230072969 + 3 ^ 40 * 374610 * 2
def baseEnd_374610 : Nat := 85491105769282031267647

theorem tailTrace_374610 : CollatzResearch.WordTrace tailWord_374610 prefixEnd_374610 85491105769282031267647 := by
  unfold tailWord_374610
  simp only [CollatzResearch.WordTrace]
  refine ⟨3415787293214855784884321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9108766115239615426358189 3415787293214855784884321)
  ·
    refine ⟨2561840469911141838663241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3415787293214855784884321 2561840469911141838663241)
    ·
      refine ⟨1921380352433356378997431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2561840469911141838663241 1921380352433356378997431)
      ·
        refine ⟨2882070528650034568496147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1921380352433356378997431 2882070528650034568496147)
        ·
          refine ⟨4323105792975051852744221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2882070528650034568496147 4323105792975051852744221)
          ·
            refine ⟨1621164672365644444779083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4323105792975051852744221 1621164672365644444779083)
            ·
              refine ⟨2431747008548466667168625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1621164672365644444779083 2431747008548466667168625)
              ·
                refine ⟨1823810256411350000376469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2431747008548466667168625 1823810256411350000376469)
                ·
                  refine ⟨85491105769282031267647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1823810256411350000376469 85491105769282031267647)
                  ·
                    rfl

theorem cell21_374610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_374610 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_374610 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_374610 prefixEnd_374610 := by exact prefixLift 374610
  have htrace : WordTrace (prefixWord ++ tailWord_374610) baseStart_374610 baseEnd_374610 := by
    simpa [prefixWord, tailWord_374610, baseEnd_374610] using wordTrace_append hprefix tailTrace_374610
  have hstable : (prefixWord ++ tailWord_374610).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374610).length < 2 ^ (prefixWord ++ tailWord_374610).sum := by decide
  have hdescent : baseEnd_374610 < baseStart_374610 := by decide
  rcases family_descends (prefixWord ++ tailWord_374610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374613 : List Nat := [1, 3, 2, 2, 2, 2, 3, 3, 3]
def baseStart_374613 : Nat := 118140960795 + 374613 * 2 ^ 59
def prefixEnd_374613 : Nat := 4983230072969 + 3 ^ 40 * 374613 * 2
def baseEnd_374613 : Nat := 85491790410154692717641

theorem tailTrace_374613 : CollatzResearch.WordTrace tailWord_374613 prefixEnd_374613 85491790410154692717641 := by
  unfold tailWord_374613
  simp only [CollatzResearch.WordTrace]
  refine ⟨13663258591848554651896493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9108839061232369767930995 13663258591848554651896493)
  ·
    refine ⟨5123721971943207994461185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13663258591848554651896493 5123721971943207994461185)
    ·
      refine ⟨3842791478957405995845889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5123721971943207994461185 3842791478957405995845889)
      ·
        refine ⟨2882093609218054496884417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3842791478957405995845889 2882093609218054496884417)
        ·
          refine ⟨2161570206913540872663313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2882093609218054496884417 2161570206913540872663313)
          ·
            refine ⟨1621177655185155654497485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2161570206913540872663313 1621177655185155654497485)
            ·
              refine ⟨607941620694433370436557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1621177655185155654497485 607941620694433370436557)
              ·
                refine ⟨227978107760412513913709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 607941620694433370436557 227978107760412513913709)
                ·
                  refine ⟨85491790410154692717641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 227978107760412513913709 85491790410154692717641)
                  ·
                    rfl

theorem cell21_374613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 3, 3].length) (baseStart_374613 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_374613 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_374613 prefixEnd_374613 := by exact prefixLift 374613
  have htrace : WordTrace (prefixWord ++ tailWord_374613) baseStart_374613 baseEnd_374613 := by
    simpa [prefixWord, tailWord_374613, baseEnd_374613] using wordTrace_append hprefix tailTrace_374613
  have hstable : (prefixWord ++ tailWord_374613).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374613).length < 2 ^ (prefixWord ++ tailWord_374613).sum := by decide
  have hdescent : baseEnd_374613 < baseStart_374613 := by decide
  rcases family_descends (prefixWord ++ tailWord_374613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374624 : List Nat := [2, 1, 1, 3, 3, 2, 9]
def baseStart_374624 : Nat := 118140960795 + 374624 * 2 ^ 59
def prefixEnd_374624 : Nat := 4983230072969 + 3 ^ 40 * 374624 * 2
def baseEnd_374624 : Nat := 9499366751113457559365

theorem tailTrace_374624 : CollatzResearch.WordTrace tailWord_374624 prefixEnd_374624 9499366751113457559365 := by
  unfold tailWord_374624
  simp only [CollatzResearch.WordTrace]
  refine ⟨6831829897404351765273463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9109106529872469020364617 6831829897404351765273463)
  ·
    refine ⟨10247744846106527647910195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6831829897404351765273463 10247744846106527647910195)
    ·
      refine ⟨15371617269159791471865293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10247744846106527647910195 15371617269159791471865293)
      ·
        refine ⟨5764356475934921801949485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15371617269159791471865293 5764356475934921801949485)
        ·
          refine ⟨2161633678475595675731057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5764356475934921801949485 2161633678475595675731057)
          ·
            refine ⟨1621225258856696756798293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2161633678475595675731057 1621225258856696756798293)
            ·
              refine ⟨9499366751113457559365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1621225258856696756798293 9499366751113457559365)
              ·
                rfl

theorem cell21_374624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 9].length) (baseStart_374624 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_374624 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_374624 prefixEnd_374624 := by exact prefixLift 374624
  have htrace : WordTrace (prefixWord ++ tailWord_374624) baseStart_374624 baseEnd_374624 := by
    simpa [prefixWord, tailWord_374624, baseEnd_374624] using wordTrace_append hprefix tailTrace_374624
  have hstable : (prefixWord ++ tailWord_374624).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374624).length < 2 ^ (prefixWord ++ tailWord_374624).sum := by decide
  have hdescent : baseEnd_374624 < baseStart_374624 := by decide
  rcases family_descends (prefixWord ++ tailWord_374624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374678 : List Nat := [5, 3, 1, 1, 2, 1, 2, 2, 4]
def baseStart_374678 : Nat := 118140960795 + 374678 * 2 ^ 59
def prefixEnd_374678 : Nat := 4983230072969 + 3 ^ 40 * 374678 * 2
def baseEnd_374678 : Nat := 85506624295729024134175

theorem tailTrace_374678 : CollatzResearch.WordTrace tailWord_374678 prefixEnd_374678 85506624295729024134175 := by
  unfold tailWord_374678
  simp only [CollatzResearch.WordTrace]
  refine ⟨854101833538316922063293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9110419557742047168675125 854101833538316922063293)
  ·
    refine ⟨320288187576868845773735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 854101833538316922063293 320288187576868845773735)
    ·
      refine ⟨480432281365303268660603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320288187576868845773735 480432281365303268660603)
      ·
        refine ⟨720648422047954902990905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 480432281365303268660603 720648422047954902990905)
        ·
          refine ⟨540486316535966177243179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 720648422047954902990905 540486316535966177243179)
          ·
            refine ⟨810729474803949265864769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 540486316535966177243179 810729474803949265864769)
            ·
              refine ⟨608047106102961949398577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 810729474803949265864769 608047106102961949398577)
              ·
                refine ⟨456035329577221462048933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 608047106102961949398577 456035329577221462048933)
                ·
                  refine ⟨85506624295729024134175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 456035329577221462048933 85506624295729024134175)
                  ·
                    rfl

theorem cell21_374678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_374678 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_374678 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_374678 prefixEnd_374678 := by exact prefixLift 374678
  have htrace : WordTrace (prefixWord ++ tailWord_374678) baseStart_374678 baseEnd_374678 := by
    simpa [prefixWord, tailWord_374678, baseEnd_374678] using wordTrace_append hprefix tailTrace_374678
  have hstable : (prefixWord ++ tailWord_374678).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374678).length < 2 ^ (prefixWord ++ tailWord_374678).sum := by decide
  have hdescent : baseEnd_374678 < baseStart_374678 := by decide
  rcases family_descends (prefixWord ++ tailWord_374678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374782 : List Nat := [4, 2, 2, 2, 1, 1, 3, 3, 3]
def baseStart_374782 : Nat := 118140960795 + 374782 * 2 ^ 59
def prefixEnd_374782 : Nat := 4983230072969 + 3 ^ 40 * 374782 * 2
def baseEnd_374782 : Nat := 85530358512647954400629

theorem tailTrace_374782 : CollatzResearch.WordTrace tailWord_374782 prefixEnd_374782 85530358512647954400629 := by
  unfold tailWord_374782
  simp only [CollatzResearch.WordTrace]
  refine ⟨1708677816029537064349825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9112948352157531009865733 1708677816029537064349825)
  ·
    refine ⟨1281508362022152798262369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1708677816029537064349825 1281508362022152798262369)
    ·
      refine ⟨961131271516614598696777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1281508362022152798262369 961131271516614598696777)
      ·
        refine ⟨720848453637460949022583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 961131271516614598696777 720848453637460949022583)
        ·
          refine ⟨1081272680456191423533875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 720848453637460949022583 1081272680456191423533875)
          ·
            refine ⟨1621909020684287135300813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1081272680456191423533875 1621909020684287135300813)
            ·
              refine ⟨608215882756607675737805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1621909020684287135300813 608215882756607675737805)
              ·
                refine ⟨228080956033727878401677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 608215882756607675737805 228080956033727878401677)
                ·
                  refine ⟨85530358512647954400629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 228080956033727878401677 85530358512647954400629)
                  ·
                    rfl

theorem cell21_374782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_374782 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_374782 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_374782 prefixEnd_374782 := by exact prefixLift 374782
  have htrace : WordTrace (prefixWord ++ tailWord_374782) baseStart_374782 baseEnd_374782 := by
    simpa [prefixWord, tailWord_374782, baseEnd_374782] using wordTrace_append hprefix tailTrace_374782
  have hstable : (prefixWord ++ tailWord_374782).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374782).length < 2 ^ (prefixWord ++ tailWord_374782).sum := by decide
  have hdescent : baseEnd_374782 < baseStart_374782 := by decide
  rcases family_descends (prefixWord ++ tailWord_374782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374869 : List Nat := [1, 3, 2, 2, 1, 5, 1, 6]
def baseStart_374869 : Nat := 118140960795 + 374869 * 2 ^ 59
def prefixEnd_374869 : Nat := 4983230072969 + 3 ^ 40 * 374869 * 2
def baseEnd_374869 : Nat := 28516737699318378816817

theorem tailTrace_374869 : CollatzResearch.WordTrace tailWord_374869 prefixEnd_374869 28516737699318378816817 := by
  unfold tailWord_374869
  simp only [CollatzResearch.WordTrace]
  refine ⟨13672595678921110373215661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9115063785947406915477107 13672595678921110373215661)
  ·
    refine ⟨5127223379595416389955873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13672595678921110373215661 5127223379595416389955873)
    ·
      refine ⟨3845417534696562292466905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5127223379595416389955873 3845417534696562292466905)
      ·
        refine ⟨2884063151022421719350179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3845417534696562292466905 2884063151022421719350179)
        ·
          refine ⟨4326094726533632579025269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2884063151022421719350179 4326094726533632579025269)
          ·
            refine ⟨405571380612528054283619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4326094726533632579025269 405571380612528054283619)
            ·
              refine ⟨608357070918792081425429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 405571380612528054283619 608357070918792081425429)
              ·
                refine ⟨28516737699318378816817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 608357070918792081425429 28516737699318378816817)
                ·
                  rfl

theorem cell21_374869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 6].length) (baseStart_374869 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_374869 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_374869 prefixEnd_374869 := by exact prefixLift 374869
  have htrace : WordTrace (prefixWord ++ tailWord_374869) baseStart_374869 baseEnd_374869 := by
    simpa [prefixWord, tailWord_374869, baseEnd_374869] using wordTrace_append hprefix tailTrace_374869
  have hstable : (prefixWord ++ tailWord_374869).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374869).length < 2 ^ (prefixWord ++ tailWord_374869).sum := by decide
  have hdescent : baseEnd_374869 < baseStart_374869 := by decide
  rcases family_descends (prefixWord ++ tailWord_374869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374897 : List Nat := [1, 2, 2, 2, 1, 1, 4, 2, 6]
def baseStart_374897 : Nat := 118140960795 + 374897 * 2 ^ 59
def prefixEnd_374897 : Nat := 4983230072969 + 3 ^ 40 * 374897 * 2
def baseEnd_374897 : Nat := 85556603079433309983727

theorem tailTrace_374897 : CollatzResearch.WordTrace tailWord_374897 prefixEnd_374897 85556603079433309983727 := by
  unfold tailWord_374897
  simp only [CollatzResearch.WordTrace]
  refine ⟨13673616922819671155234945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9115744615213114103489963 13673616922819671155234945)
  ·
    refine ⟨10255212692114753366426209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13673616922819671155234945 10255212692114753366426209)
    ·
      refine ⟨7691409519086065024819657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10255212692114753366426209 7691409519086065024819657)
      ·
        refine ⟨5768557139314548768614743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7691409519086065024819657 5768557139314548768614743)
        ·
          refine ⟨8652835708971823152922115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5768557139314548768614743 8652835708971823152922115)
          ·
            refine ⟨12979253563457734729383173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8652835708971823152922115 12979253563457734729383173)
            ·
              refine ⟨2433610043148325261759345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12979253563457734729383173 2433610043148325261759345)
              ·
                refine ⟨1825207532361243946319509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2433610043148325261759345 1825207532361243946319509)
                ·
                  refine ⟨85556603079433309983727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1825207532361243946319509 85556603079433309983727)
                  ·
                    rfl

theorem cell21_374897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 6].length) (baseStart_374897 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_374897 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_374897 prefixEnd_374897 := by exact prefixLift 374897
  have htrace : WordTrace (prefixWord ++ tailWord_374897) baseStart_374897 baseEnd_374897 := by
    simpa [prefixWord, tailWord_374897, baseEnd_374897] using wordTrace_append hprefix tailTrace_374897
  have hstable : (prefixWord ++ tailWord_374897).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374897).length < 2 ^ (prefixWord ++ tailWord_374897).sum := by decide
  have hdescent : baseEnd_374897 < baseStart_374897 := by decide
  rcases family_descends (prefixWord ++ tailWord_374897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374945 : List Nat := [1, 2, 3, 3, 1, 2, 4, 5]
def baseStart_374945 : Nat := 118140960795 + 374945 * 2 ^ 59
def prefixEnd_374945 : Nat := 4983230072969 + 3 ^ 40 * 374945 * 2
def baseEnd_374945 : Nat := 28522519111131964394543

theorem tailTrace_374945 : CollatzResearch.WordTrace tailWord_374945 prefixEnd_374945 28522519111131964394543 := by
  unfold tailWord_374945
  simp only [CollatzResearch.WordTrace]
  refine ⟨13675367626645775352982289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9116911751097183568654859 13675367626645775352982289)
  ·
    refine ⟨10256525719984331514736717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13675367626645775352982289 10256525719984331514736717)
    ·
      refine ⟨3846197144994124318026269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10256525719984331514736717 3846197144994124318026269)
      ·
        refine ⟨1442323929372796619259851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3846197144994124318026269 1442323929372796619259851)
        ·
          refine ⟨2163485894059194928889777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1442323929372796619259851 2163485894059194928889777)
          ·
            refine ⟨1622614420544396196667333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2163485894059194928889777 1622614420544396196667333)
            ·
              refine ⟨304240203852074286875125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1622614420544396196667333 304240203852074286875125)
              ·
                refine ⟨28522519111131964394543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 304240203852074286875125 28522519111131964394543)
                ·
                  rfl

theorem cell21_374945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4, 5].length) (baseStart_374945 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_374945 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_374945 prefixEnd_374945 := by exact prefixLift 374945
  have htrace : WordTrace (prefixWord ++ tailWord_374945) baseStart_374945 baseEnd_374945 := by
    simpa [prefixWord, tailWord_374945, baseEnd_374945] using wordTrace_append hprefix tailTrace_374945
  have hstable : (prefixWord ++ tailWord_374945).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374945).length < 2 ^ (prefixWord ++ tailWord_374945).sum := by decide
  have hdescent : baseEnd_374945 < baseStart_374945 := by decide
  rcases family_descends (prefixWord ++ tailWord_374945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374951 : List Nat := [1, 1, 6, 2, 3, 1, 1, 3, 3]
def baseStart_374951 : Nat := 118140960795 + 374951 * 2 ^ 59
def prefixEnd_374951 : Nat := 4983230072969 + 3 ^ 40 * 374951 * 2
def baseEnd_374951 : Nat := 85568926615141216083617

theorem tailTrace_374951 : CollatzResearch.WordTrace tailWord_374951 prefixEnd_374951 85568926615141216083617 := by
  unfold tailWord_374951
  simp only [CollatzResearch.WordTrace]
  refine ⟨13675586464624038377700707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9117057643082692251800471 13675586464624038377700707)
  ·
    refine ⟨20513379696936057566551061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13675586464624038377700707 20513379696936057566551061)
    ·
      refine ⟨961564673293877698432081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 20513379696936057566551061 961564673293877698432081)
      ·
        refine ⟨721173504970408273824061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 961564673293877698432081 721173504970408273824061)
        ·
          refine ⟨270440064363903102684023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 721173504970408273824061 270440064363903102684023)
          ·
            refine ⟨405660096545854654026035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270440064363903102684023 405660096545854654026035)
            ·
              refine ⟨608490144818781981039053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 405660096545854654026035 608490144818781981039053)
              ·
                refine ⟨228183804307043242889645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 608490144818781981039053 228183804307043242889645)
                ·
                  refine ⟨85568926615141216083617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 228183804307043242889645 85568926615141216083617)
                  ·
                    rfl

theorem cell21_374951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 3, 3].length) (baseStart_374951 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_374951 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_374951 prefixEnd_374951 := by exact prefixLift 374951
  have htrace : WordTrace (prefixWord ++ tailWord_374951) baseStart_374951 baseEnd_374951 := by
    simpa [prefixWord, tailWord_374951, baseEnd_374951] using wordTrace_append hprefix tailTrace_374951
  have hstable : (prefixWord ++ tailWord_374951).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374951).length < 2 ^ (prefixWord ++ tailWord_374951).sum := by decide
  have hdescent : baseEnd_374951 < baseStart_374951 := by decide
  rcases family_descends (prefixWord ++ tailWord_374951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374976 : List Nat := [2, 1, 1, 2, 5, 3, 1, 1, 5]
def baseStart_374976 : Nat := 118140960795 + 374976 * 2 ^ 59
def prefixEnd_374976 : Nat := 4983230072969 + 3 ^ 40 * 374976 * 2
def baseEnd_374976 : Nat := 85574631955746728166899

theorem tailTrace_374976 : CollatzResearch.WordTrace tailWord_374976 prefixEnd_374976 85574631955746728166899 := by
  unfold tailWord_374976
  simp only [CollatzResearch.WordTrace]
  refine ⟨6838249144766733823680391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9117665526355645098240521 6838249144766733823680391)
  ·
    refine ⟨10257373717150100735520587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6838249144766733823680391 10257373717150100735520587)
    ·
      refine ⟨15386060575725151103280881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10257373717150100735520587 15386060575725151103280881)
      ·
        refine ⟨11539545431793863327460661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15386060575725151103280881 11539545431793863327460661)
        ·
          refine ⟨1081832384230674686949437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11539545431793863327460661 1081832384230674686949437)
          ·
            refine ⟨405687144086503007606039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1081832384230674686949437 405687144086503007606039)
            ·
              refine ⟨608530716129754511409059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 405687144086503007606039 608530716129754511409059)
              ·
                refine ⟨912796074194631767113589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 608530716129754511409059 912796074194631767113589)
                ·
                  refine ⟨85574631955746728166899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 912796074194631767113589 85574631955746728166899)
                  ·
                    rfl

theorem cell21_374976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 1, 5].length) (baseStart_374976 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_374976 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_374976 prefixEnd_374976 := by exact prefixLift 374976
  have htrace : WordTrace (prefixWord ++ tailWord_374976) baseStart_374976 baseEnd_374976 := by
    simpa [prefixWord, tailWord_374976, baseEnd_374976] using wordTrace_append hprefix tailTrace_374976
  have hstable : (prefixWord ++ tailWord_374976).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374976).length < 2 ^ (prefixWord ++ tailWord_374976).sum := by decide
  have hdescent : baseEnd_374976 < baseStart_374976 := by decide
  rcases family_descends (prefixWord ++ tailWord_374976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375021 : List Nat := [1, 5, 1, 2, 4, 8]
def baseStart_375021 : Nat := 118140960795 + 375021 * 2 ^ 59
def prefixEnd_375021 : Nat := 4983230072969 + 3 ^ 40 * 375021 * 2
def baseEnd_375021 : Nat := 3169811169216172219141

theorem tailTrace_375021 : CollatzResearch.WordTrace tailWord_375021 prefixEnd_375021 3169811169216172219141 := by
  unfold tailWord_375021
  simp only [CollatzResearch.WordTrace]
  refine ⟨13678139574370440332748917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9118759716246960221832611 13678139574370440332748917)
  ·
    refine ⟨1282325585097228781195211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13678139574370440332748917 1282325585097228781195211)
    ·
      refine ⟨1923488377645843171792817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1282325585097228781195211 1923488377645843171792817)
      ·
        refine ⟨1442616283234382378844613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1923488377645843171792817 1442616283234382378844613)
        ·
          refine ⟨270490553106446696033365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1442616283234382378844613 270490553106446696033365)
          ·
            refine ⟨3169811169216172219141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 270490553106446696033365 3169811169216172219141)
            ·
              rfl

theorem cell21_375021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 8].length) (baseStart_375021 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_375021 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_375021 prefixEnd_375021 := by exact prefixLift 375021
  have htrace : WordTrace (prefixWord ++ tailWord_375021) baseStart_375021 baseEnd_375021 := by
    simpa [prefixWord, tailWord_375021, baseEnd_375021] using wordTrace_append hprefix tailTrace_375021
  have hstable : (prefixWord ++ tailWord_375021).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375021).length < 2 ^ (prefixWord ++ tailWord_375021).sum := by decide
  have hdescent : baseEnd_375021 < baseStart_375021 := by decide
  rcases family_descends (prefixWord ++ tailWord_375021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375190 : List Nat := [5, 3, 1, 2, 10]
def baseStart_375190 : Nat := 118140960795 + 375190 * 2 ^ 59
def prefixEnd_375190 : Nat := 4983230072969 + 3 ^ 40 * 375190 * 2
def baseEnd_375190 : Nat := 1057079872485554464195

theorem tailTrace_375190 : CollatzResearch.WordTrace tailWord_375190 prefixEnd_375190 1057079872485554464195 := by
  unfold tailWord_375190
  simp only [CollatzResearch.WordTrace]
  refine ⟨855268969422386387228189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9122869007172121463767349 855268969422386387228189)
  ·
    refine ⟨320725863533394895210571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 855268969422386387228189 320725863533394895210571)
    ·
      refine ⟨481088795300092342815857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320725863533394895210571 481088795300092342815857)
      ·
        refine ⟨360816596475069257111893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 481088795300092342815857 360816596475069257111893)
        ·
          refine ⟨1057079872485554464195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 360816596475069257111893 1057079872485554464195)
          ·
            rfl

theorem cell21_375190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 10].length) (baseStart_375190 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_375190 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_375190 prefixEnd_375190 := by exact prefixLift 375190
  have htrace : WordTrace (prefixWord ++ tailWord_375190) baseStart_375190 baseEnd_375190 := by
    simpa [prefixWord, tailWord_375190, baseEnd_375190] using wordTrace_append hprefix tailTrace_375190
  have hstable : (prefixWord ++ tailWord_375190).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375190).length < 2 ^ (prefixWord ++ tailWord_375190).sum := by decide
  have hdescent : baseEnd_375190 < baseStart_375190 := by decide
  rcases family_descends (prefixWord ++ tailWord_375190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375246 : List Nat := [4, 1, 1, 1, 2, 1, 1, 1, 9]
def baseStart_375246 : Nat := 118140960795 + 375246 * 2 ^ 59
def prefixEnd_375246 : Nat := 4983230072969 + 3 ^ 40 * 375246 * 2
def baseEnd_375246 : Nat := 85636249634286258666347

theorem tailTrace_375246 : CollatzResearch.WordTrace tailWord_375246 prefixEnd_375246 85636249634286258666347 := by
  unfold tailWord_375246
  simp only [CollatzResearch.WordTrace]
  refine ⟨1710793249819412969961199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9124230665703535839793061 1710793249819412969961199)
  ·
    refine ⟨2566189874729119454941799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1710793249819412969961199 2566189874729119454941799)
    ·
      refine ⟨3849284812093679182412699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2566189874729119454941799 3849284812093679182412699)
      ·
        refine ⟨5773927218140518773619049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3849284812093679182412699 5773927218140518773619049)
        ·
          refine ⟨4330445413605389080214287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5773927218140518773619049 4330445413605389080214287)
          ·
            refine ⟨6495668120408083620321431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4330445413605389080214287 6495668120408083620321431)
            ·
              refine ⟨9743502180612125430482147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6495668120408083620321431 9743502180612125430482147)
              ·
                refine ⟨14615253270918188145723221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9743502180612125430482147 14615253270918188145723221)
                ·
                  refine ⟨85636249634286258666347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 14615253270918188145723221 85636249634286258666347)
                  ·
                    rfl

theorem cell21_375246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_375246 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_375246 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_375246 prefixEnd_375246 := by exact prefixLift 375246
  have htrace : WordTrace (prefixWord ++ tailWord_375246) baseStart_375246 baseEnd_375246 := by
    simpa [prefixWord, tailWord_375246, baseEnd_375246] using wordTrace_append hprefix tailTrace_375246
  have hstable : (prefixWord ++ tailWord_375246).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375246).length < 2 ^ (prefixWord ++ tailWord_375246).sum := by decide
  have hdescent : baseEnd_375246 < baseStart_375246 := by decide
  rcases family_descends (prefixWord ++ tailWord_375246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375263 : List Nat := [1, 1, 2, 3, 3, 3, 2, 1, 5]
def baseStart_375263 : Nat := 118140960795 + 375263 * 2 ^ 59
def prefixEnd_375263 : Nat := 4983230072969 + 3 ^ 40 * 375263 * 2
def baseEnd_375263 : Nat := 85640129265898006882979

theorem tailTrace_375263 : CollatzResearch.WordTrace tailWord_375263 prefixEnd_375263 85640129265898006882979 := by
  unfold tailWord_375263
  simp only [CollatzResearch.WordTrace]
  refine ⟨13686966039493715663058443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9124644026329143775372295 13686966039493715663058443)
  ·
    refine ⟨20530449059240573494587665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13686966039493715663058443 20530449059240573494587665)
    ·
      refine ⟨15397836794430430120940749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20530449059240573494587665 15397836794430430120940749)
      ·
        refine ⟨5774188797911411295352781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15397836794430430120940749 5774188797911411295352781)
        ·
          refine ⟨2165320799216779235757293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5774188797911411295352781 2165320799216779235757293)
          ·
            refine ⟨811995299706292213408985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2165320799216779235757293 811995299706292213408985)
            ·
              refine ⟨608996474779719160056739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 811995299706292213408985 608996474779719160056739)
              ·
                refine ⟨913494712169578740085109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 608996474779719160056739 913494712169578740085109)
                ·
                  refine ⟨85640129265898006882979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 913494712169578740085109 85640129265898006882979)
                  ·
                    rfl

theorem cell21_375263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 1, 5].length) (baseStart_375263 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_375263 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_375263 prefixEnd_375263 := by exact prefixLift 375263
  have htrace : WordTrace (prefixWord ++ tailWord_375263) baseStart_375263 baseEnd_375263 := by
    simpa [prefixWord, tailWord_375263, baseEnd_375263] using wordTrace_append hprefix tailTrace_375263
  have hstable : (prefixWord ++ tailWord_375263).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375263).length < 2 ^ (prefixWord ++ tailWord_375263).sum := by decide
  have hdescent : baseEnd_375263 < baseStart_375263 := by decide
  rcases family_descends (prefixWord ++ tailWord_375263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375297 : List Nat := [1, 2, 4, 1, 3, 3, 1, 3, 3]
def baseStart_375297 : Nat := 118140960795 + 375297 * 2 ^ 59
def prefixEnd_375297 : Nat := 4983230072969 + 3 ^ 40 * 375297 * 2
def baseEnd_375297 : Nat := 85647888529121503316243

theorem tailTrace_375297 : CollatzResearch.WordTrace tailWord_375297 prefixEnd_375297 85647888529121503316243 := by
  unfold tailWord_375297
  simp only [CollatzResearch.WordTrace]
  refine ⟨13688206121370539469796145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9125470747580359646530763 13688206121370539469796145)
  ·
    refine ⟨10266154591027904602347109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13688206121370539469796145 10266154591027904602347109)
    ·
      refine ⟨1924903985817732112940083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10266154591027904602347109 1924903985817732112940083)
      ·
        refine ⟨2887355978726598169410125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1924903985817732112940083 2887355978726598169410125)
        ·
          refine ⟨1082758492022474313528797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2887355978726598169410125 1082758492022474313528797)
          ·
            refine ⟨406034434508427867573299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1082758492022474313528797 406034434508427867573299)
            ·
              refine ⟨609051651762641801359949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 406034434508427867573299 609051651762641801359949)
              ·
                refine ⟨228394369410990675509981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 609051651762641801359949 228394369410990675509981)
                ·
                  refine ⟨85647888529121503316243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 228394369410990675509981 85647888529121503316243)
                  ·
                    rfl

theorem cell21_375297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 3, 3].length) (baseStart_375297 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_375297 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_375297 prefixEnd_375297 := by exact prefixLift 375297
  have htrace : WordTrace (prefixWord ++ tailWord_375297) baseStart_375297 baseEnd_375297 := by
    simpa [prefixWord, tailWord_375297, baseEnd_375297] using wordTrace_append hprefix tailTrace_375297
  have hstable : (prefixWord ++ tailWord_375297).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375297).length < 2 ^ (prefixWord ++ tailWord_375297).sum := by decide
  have hdescent : baseEnd_375297 < baseStart_375297 := by decide
  rcases family_descends (prefixWord ++ tailWord_375297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375308 : List Nat := [2, 2, 1, 2, 4, 3, 7]
def baseStart_375308 : Nat := 118140960795 + 375308 * 2 ^ 59
def prefixEnd_375308 : Nat := 4983230072969 + 3 ^ 40 * 375308 * 2
def baseEnd_375308 : Nat := 9516710986554214292543

theorem tailTrace_375308 : CollatzResearch.WordTrace tailWord_375308 prefixEnd_375308 9516710986554214292543 := by
  unfold tailWord_375308
  simp only [CollatzResearch.WordTrace]
  refine ⟨6844303662165344174223289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9125738216220458898964385 6844303662165344174223289)
  ·
    refine ⟨5133227746624008130667467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6844303662165344174223289 5133227746624008130667467)
    ·
      refine ⟨7699841619936012196001201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5133227746624008130667467 7699841619936012196001201)
      ·
        refine ⟨5774881214952009147000901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7699841619936012196001201 5774881214952009147000901)
        ·
          refine ⟨1082790227803501715062669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5774881214952009147000901 1082790227803501715062669)
          ·
            refine ⟨406046335426313143148501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1082790227803501715062669 406046335426313143148501)
            ·
              refine ⟨9516710986554214292543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 406046335426313143148501 9516710986554214292543)
              ·
                rfl

theorem cell21_375308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 7].length) (baseStart_375308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_375308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_375308 prefixEnd_375308 := by exact prefixLift 375308
  have htrace : WordTrace (prefixWord ++ tailWord_375308) baseStart_375308 baseEnd_375308 := by
    simpa [prefixWord, tailWord_375308, baseEnd_375308] using wordTrace_append hprefix tailTrace_375308
  have hstable : (prefixWord ++ tailWord_375308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375308).length < 2 ^ (prefixWord ++ tailWord_375308).sum := by decide
  have hdescent : baseEnd_375308 < baseStart_375308 := by decide
  rcases family_descends (prefixWord ++ tailWord_375308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375328 : List Nat := [2, 1, 1, 6, 2, 2, 2, 1, 4]
def baseStart_375328 : Nat := 118140960795 + 375328 * 2 ^ 59
def prefixEnd_375328 : Nat := 4983230072969 + 3 ^ 40 * 375328 * 2
def baseEnd_375328 : Nat := 85654963151472338299513

theorem tailTrace_375328 : CollatzResearch.WordTrace tailWord_375328 prefixEnd_375328 85654963151472338299513 := by
  unfold tailWord_375328
  simp only [CollatzResearch.WordTrace]
  refine ⟨6844668392129115882087319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9126224522838821176116425 6844668392129115882087319)
  ·
    refine ⟨10267002588193673823130979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6844668392129115882087319 10267002588193673823130979)
    ·
      refine ⟨15400503882290510734696469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10267002588193673823130979 15400503882290510734696469)
      ·
        refine ⟨721898619482367690688897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 15400503882290510734696469 721898619482367690688897)
        ·
          refine ⟨541423964611775768016673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 721898619482367690688897 541423964611775768016673)
          ·
            refine ⟨406067973458831826012505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 541423964611775768016673 406067973458831826012505)
            ·
              refine ⟨304550980094123869509379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 406067973458831826012505 304550980094123869509379)
              ·
                refine ⟨456826470141185804264069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 304550980094123869509379 456826470141185804264069)
                ·
                  refine ⟨85654963151472338299513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 456826470141185804264069 85654963151472338299513)
                  ·
                    rfl

theorem cell21_375328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2, 1, 4].length) (baseStart_375328 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_375328 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_375328 prefixEnd_375328 := by exact prefixLift 375328
  have htrace : WordTrace (prefixWord ++ tailWord_375328) baseStart_375328 baseEnd_375328 := by
    simpa [prefixWord, tailWord_375328, baseEnd_375328] using wordTrace_append hprefix tailTrace_375328
  have hstable : (prefixWord ++ tailWord_375328).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375328).length < 2 ^ (prefixWord ++ tailWord_375328).sum := by decide
  have hdescent : baseEnd_375328 < baseStart_375328 := by decide
  rcases family_descends (prefixWord ++ tailWord_375328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375367 : List Nat := [1, 1, 4, 1, 4, 10]
def baseStart_375367 : Nat := 118140960795 + 375367 * 2 ^ 59
def prefixEnd_375367 : Nat := 4983230072969 + 3 ^ 40 * 375367 * 2
def baseEnd_375367 : Nat := 3172735684548775449979

theorem tailTrace_375367 : CollatzResearch.WordTrace tailWord_375367 prefixEnd_375367 3172735684548775449979 := by
  unfold tailWord_375367
  simp only [CollatzResearch.WordTrace]
  refine ⟨13690759231116941424844355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9127172820744627616562903 13690759231116941424844355)
  ·
    refine ⟨20536138846675412137266533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13690759231116941424844355 20536138846675412137266533)
    ·
      refine ⟨3850526033751639775737475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20536138846675412137266533 3850526033751639775737475)
      ·
        refine ⟨5775789050627459663606213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3850526033751639775737475 5775789050627459663606213)
        ·
          refine ⟨1082960446992648686926165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5775789050627459663606213 1082960446992648686926165)
          ·
            refine ⟨3172735684548775449979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1082960446992648686926165 3172735684548775449979)
            ·
              rfl

theorem cell21_375367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 10].length) (baseStart_375367 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_375367 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_375367 prefixEnd_375367 := by exact prefixLift 375367
  have htrace : WordTrace (prefixWord ++ tailWord_375367) baseStart_375367 baseEnd_375367 := by
    simpa [prefixWord, tailWord_375367, baseEnd_375367] using wordTrace_append hprefix tailTrace_375367
  have hstable : (prefixWord ++ tailWord_375367).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375367).length < 2 ^ (prefixWord ++ tailWord_375367).sum := by decide
  have hdescent : baseEnd_375367 < baseStart_375367 := by decide
  rcases family_descends (prefixWord ++ tailWord_375367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375370 : List Nat := [3, 1, 2, 1, 1, 5, 2, 2, 4]
def baseStart_375370 : Nat := 118140960795 + 375370 * 2 ^ 59
def prefixEnd_375370 : Nat := 4983230072969 + 3 ^ 40 * 375370 * 2
def baseEnd_375370 : Nat := 85664548123689598599427

theorem tailTrace_375370 : CollatzResearch.WordTrace tailWord_375370 prefixEnd_375370 85664548123689598599427 := by
  unfold tailWord_375370
  simp only [CollatzResearch.WordTrace]
  refine ⟨3422717162526518234300891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9127245766737381958135709 3422717162526518234300891)
  ·
    refine ⟨5134075743789777351451337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3422717162526518234300891 5134075743789777351451337)
    ·
      refine ⟨3850556807842333013588503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5134075743789777351451337 3850556807842333013588503)
      ·
        refine ⟨5775835211763499520382755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3850556807842333013588503 5775835211763499520382755)
        ·
          refine ⟨8663752817645249280574133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5775835211763499520382755 8663752817645249280574133)
          ·
            refine ⟨812226826654242120053825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8663752817645249280574133 812226826654242120053825)
            ·
              refine ⟨609170119990681590040369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 812226826654242120053825 609170119990681590040369)
              ·
                refine ⟨456877589993011192530277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 609170119990681590040369 456877589993011192530277)
                ·
                  refine ⟨85664548123689598599427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 456877589993011192530277 85664548123689598599427)
                  ·
                    rfl

theorem cell21_375370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 2, 4].length) (baseStart_375370 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_375370 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_375370 prefixEnd_375370 := by exact prefixLift 375370
  have htrace : WordTrace (prefixWord ++ tailWord_375370) baseStart_375370 baseEnd_375370 := by
    simpa [prefixWord, tailWord_375370, baseEnd_375370] using wordTrace_append hprefix tailTrace_375370
  have hstable : (prefixWord ++ tailWord_375370).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375370).length < 2 ^ (prefixWord ++ tailWord_375370).sum := by decide
  have hdescent : baseEnd_375370 < baseStart_375370 := by decide
  rcases family_descends (prefixWord ++ tailWord_375370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375373 : List Nat := [1, 6, 1, 1, 2, 2, 1, 4, 3]
def baseStart_375373 : Nat := 118140960795 + 375373 * 2 ^ 59
def prefixEnd_375373 : Nat := 4983230072969 + 3 ^ 40 * 375373 * 2
def baseEnd_375373 : Nat := 85665232764562260049421

theorem tailTrace_375373 : CollatzResearch.WordTrace tailWord_375373 prefixEnd_375373 85665232764562260049421 := by
  unfold tailWord_375373
  simp only [CollatzResearch.WordTrace]
  refine ⟨13690978069095204449562773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9127318712730136299708515 13690978069095204449562773)
  ·
    refine ⟨641764596988837708573255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 13690978069095204449562773 641764596988837708573255)
    ·
      refine ⟨962646895483256562859883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 641764596988837708573255 962646895483256562859883)
      ·
        refine ⟨1443970343224884844289825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 962646895483256562859883 1443970343224884844289825)
        ·
          refine ⟨1082977757418663633217369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1443970343224884844289825 1082977757418663633217369)
          ·
            refine ⟨812233318063997724913027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1082977757418663633217369 812233318063997724913027)
            ·
              refine ⟨1218349977095996587369541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 812233318063997724913027 1218349977095996587369541)
              ·
                refine ⟨228440620705499360131789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1218349977095996587369541 228440620705499360131789)
                ·
                  refine ⟨85665232764562260049421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 228440620705499360131789 85665232764562260049421)
                  ·
                    rfl

theorem cell21_375373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_375373 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_375373 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_375373 prefixEnd_375373 := by exact prefixLift 375373
  have htrace : WordTrace (prefixWord ++ tailWord_375373) baseStart_375373 baseEnd_375373 := by
    simpa [prefixWord, tailWord_375373, baseEnd_375373] using wordTrace_append hprefix tailTrace_375373
  have hstable : (prefixWord ++ tailWord_375373).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375373).length < 2 ^ (prefixWord ++ tailWord_375373).sum := by decide
  have hdescent : baseEnd_375373 < baseStart_375373 := by decide
  rcases family_descends (prefixWord ++ tailWord_375373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375390 : List Nat := [4, 4, 1, 2, 1, 1, 1, 2, 5]
def baseStart_375390 : Nat := 118140960795 + 375390 * 2 ^ 59
def prefixEnd_375390 : Nat := 4983230072969 + 3 ^ 40 * 375390 * 2
def baseEnd_375390 : Nat := 85669112396174008266053

theorem tailTrace_375390 : CollatzResearch.WordTrace tailWord_375390 prefixEnd_375390 85669112396174008266053 := by
  unfold tailWord_375390
  simp only [CollatzResearch.WordTrace]
  refine ⟨1711449763754202044116453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9127732073355744235287749 1711449763754202044116453)
  ·
    refine ⟨320896830703912883271835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1711449763754202044116453 320896830703912883271835)
    ·
      refine ⟨481345246055869324907753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320896830703912883271835 481345246055869324907753)
      ·
        refine ⟨361008934541901993680815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 481345246055869324907753 361008934541901993680815)
        ·
          refine ⟨541513401812852990521223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 361008934541901993680815 541513401812852990521223)
          ·
            refine ⟨812270102719279485781835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 541513401812852990521223 812270102719279485781835)
            ·
              refine ⟨1218405154078919228672753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 812270102719279485781835 1218405154078919228672753)
              ·
                refine ⟨913803865559189421504565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1218405154078919228672753 913803865559189421504565)
                ·
                  refine ⟨85669112396174008266053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 913803865559189421504565 85669112396174008266053)
                  ·
                    rfl

theorem cell21_375390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_375390 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_375390 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_375390 prefixEnd_375390 := by exact prefixLift 375390
  have htrace : WordTrace (prefixWord ++ tailWord_375390) baseStart_375390 baseEnd_375390 := by
    simpa [prefixWord, tailWord_375390, baseEnd_375390] using wordTrace_append hprefix tailTrace_375390
  have hstable : (prefixWord ++ tailWord_375390).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375390).length < 2 ^ (prefixWord ++ tailWord_375390).sum := by decide
  have hdescent : baseEnd_375390 < baseStart_375390 := by decide
  rcases family_descends (prefixWord ++ tailWord_375390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375415 : List Nat := [1, 1, 3, 1, 1, 3, 3, 5, 3]
def baseStart_375415 : Nat := 118140960795 + 375415 * 2 ^ 59
def prefixEnd_375415 : Nat := 4983230072969 + 3 ^ 40 * 375415 * 2
def baseEnd_375415 : Nat := 85674817736779520349335

theorem tailTrace_375415 : CollatzResearch.WordTrace tailWord_375415 prefixEnd_375415 85674817736779520349335 := by
  unfold tailWord_375415
  simp only [CollatzResearch.WordTrace]
  refine ⟨13692509934943045622591699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9128339956628697081727799 13692509934943045622591699)
  ·
    refine ⟨20538764902414568433887549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13692509934943045622591699 20538764902414568433887549)
    ·
      refine ⟨7702036838405463162707831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20538764902414568433887549 7702036838405463162707831)
      ·
        refine ⟨11553055257608194744061747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7702036838405463162707831 11553055257608194744061747)
        ·
          refine ⟨17329582886412292116092621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11553055257608194744061747 17329582886412292116092621)
          ·
            refine ⟨6498593582404609543534733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17329582886412292116092621 6498593582404609543534733)
            ·
              refine ⟨2436972593401728578825525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6498593582404609543534733 2436972593401728578825525)
              ·
                refine ⟨228466180631412054264893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2436972593401728578825525 228466180631412054264893)
                ·
                  refine ⟨85674817736779520349335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 228466180631412054264893 85674817736779520349335)
                  ·
                    rfl

theorem cell21_375415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 5, 3].length) (baseStart_375415 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_375415 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_375415 prefixEnd_375415 := by exact prefixLift 375415
  have htrace : WordTrace (prefixWord ++ tailWord_375415) baseStart_375415 baseEnd_375415 := by
    simpa [prefixWord, tailWord_375415, baseEnd_375415] using wordTrace_append hprefix tailTrace_375415
  have hstable : (prefixWord ++ tailWord_375415).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375415).length < 2 ^ (prefixWord ++ tailWord_375415).sum := by decide
  have hdescent : baseEnd_375415 < baseStart_375415 := by decide
  rcases family_descends (prefixWord ++ tailWord_375415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
