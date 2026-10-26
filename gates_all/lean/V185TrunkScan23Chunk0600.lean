import V185TrunkScan23Chunk0599

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3546521 : List Nat := [1, 2, 1, 2, 1, 6, 1, 3, 1, 3, 2]
def baseStart_3546521 : Nat := 118140960795 + 3546521 * 2 ^ 59
def prefixEnd_3546521 : Nat := 4983230072969 + 3 ^ 40 * 3546521 * 2
def baseEnd_3546521 : Nat := 1821069924264223953977353

theorem tailTrace_3546521 : CollatzResearch.WordTrace tailWord_3546521 prefixEnd_3546521 1821069924264223953977353 := by
  unfold tailWord_3546521
  simp only [CollatzResearch.WordTrace]
  refine ⟨129352247584567589409863417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86234831723045059606575611 129352247584567589409863417)
  ·
    refine ⟨97014185688425692057397563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129352247584567589409863417 97014185688425692057397563)
    ·
      refine ⟨145521278532638538086096345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97014185688425692057397563 145521278532638538086096345)
      ·
        refine ⟨109140958899478903564572259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145521278532638538086096345 109140958899478903564572259)
        ·
          refine ⟨163711438349218355346858389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109140958899478903564572259 163711438349218355346858389)
          ·
            refine ⟨7673973672619610406883987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 163711438349218355346858389 7673973672619610406883987)
            ·
              refine ⟨11510960508929415610325981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7673973672619610406883987 11510960508929415610325981)
              ·
                refine ⟨4316610190848530853872243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11510960508929415610325981 4316610190848530853872243)
                ·
                  refine ⟨6474915286272796280808365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4316610190848530853872243 6474915286272796280808365)
                  ·
                    refine ⟨2428093232352298605303137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6474915286272796280808365 2428093232352298605303137)
                    ·
                      refine ⟨1821069924264223953977353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2428093232352298605303137 1821069924264223953977353)
                      ·
                        rfl

theorem cell23_3546521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 3, 1, 3, 2].length) (baseStart_3546521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3546521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3546521 prefixEnd_3546521 := by exact prefixLift 3546521
  have htrace : WordTrace (prefixWord ++ tailWord_3546521) baseStart_3546521 baseEnd_3546521 := by
    simpa [prefixWord, tailWord_3546521, baseEnd_3546521] using wordTrace_append hprefix tailTrace_3546521
  have hstable : (prefixWord ++ tailWord_3546521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546521).length < 2 ^ (prefixWord ++ tailWord_3546521).sum := by decide
  have hdescent : baseEnd_3546521 < baseStart_3546521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546527 : List Nat := [1, 1, 2, 5, 1, 2, 1, 2, 2, 6]
def baseStart_3546527 : Nat := 118140960795 + 3546527 * 2 ^ 59
def prefixEnd_3546527 : Nat := 4983230072969 + 3 ^ 40 * 3546527 * 2
def baseEnd_3546527 : Nat := 607024335049383643500775

theorem tailTrace_3546527 : CollatzResearch.WordTrace tailWord_3546527 prefixEnd_3546527 607024335049383643500775 := by
  unfold tailWord_3546527
  simp only [CollatzResearch.WordTrace]
  refine ⟨129352466422545852434581835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86234977615030568289721223 129352466422545852434581835)
  ·
    refine ⟨194028699633818778651872753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129352466422545852434581835 194028699633818778651872753)
    ·
      refine ⟨145521524725364083988904565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194028699633818778651872753 145521524725364083988904565)
      ·
        refine ⟨13642642943002882873959803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 145521524725364083988904565 13642642943002882873959803)
        ·
          refine ⟨20463964414504324310939705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13642642943002882873959803 20463964414504324310939705)
          ·
            refine ⟨15347973310878243233204779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20463964414504324310939705 15347973310878243233204779)
            ·
              refine ⟨23021959966317364849807169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15347973310878243233204779 23021959966317364849807169)
              ·
                refine ⟨17266469974738023637355377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23021959966317364849807169 17266469974738023637355377)
                ·
                  refine ⟨12949852481053517728016533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17266469974738023637355377 12949852481053517728016533)
                  ·
                    refine ⟨607024335049383643500775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12949852481053517728016533 607024335049383643500775)
                    ·
                      rfl

theorem cell23_3546527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 2, 6].length) (baseStart_3546527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3546527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3546527 prefixEnd_3546527 := by exact prefixLift 3546527
  have htrace : WordTrace (prefixWord ++ tailWord_3546527) baseStart_3546527 baseEnd_3546527 := by
    simpa [prefixWord, tailWord_3546527, baseEnd_3546527] using wordTrace_append hprefix tailTrace_3546527
  have hstable : (prefixWord ++ tailWord_3546527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546527).length < 2 ^ (prefixWord ++ tailWord_3546527).sum := by decide
  have hdescent : baseEnd_3546527 < baseStart_3546527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546557 : List Nat := [1, 4, 1, 2, 2, 1, 1, 4, 7]
def baseStart_3546557 : Nat := 118140960795 + 3546557 * 2 ^ 59
def prefixEnd_3546557 : Nat := 4983230072969 + 3 ^ 40 * 3546557 * 2
def baseEnd_3546557 : Nat := 202343156618642868125243

theorem tailTrace_3546557 : CollatzResearch.WordTrace tailWord_3546557 prefixEnd_3546557 202343156618642868125243 := by
  unfold tailWord_3546557
  simp only [CollatzResearch.WordTrace]
  refine ⟨129353560612437167558173925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86235707074958111705449283 129353560612437167558173925)
  ·
    refine ⟨24253792614831968917157611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129353560612437167558173925 24253792614831968917157611)
    ·
      refine ⟨36380688922247953375736417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24253792614831968917157611 36380688922247953375736417)
      ·
        refine ⟨27285516691685965031802313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36380688922247953375736417 27285516691685965031802313)
        ·
          refine ⟨20464137518764473773851735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27285516691685965031802313 20464137518764473773851735)
          ·
            refine ⟨30696206278146710660777603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20464137518764473773851735 30696206278146710660777603)
            ·
              refine ⟨46044309417220065991166405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30696206278146710660777603 46044309417220065991166405)
              ·
                refine ⟨8633308015728762373343701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46044309417220065991166405 8633308015728762373343701)
                ·
                  refine ⟨202343156618642868125243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8633308015728762373343701 202343156618642868125243)
                  ·
                    rfl

theorem cell23_3546557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 4, 7].length) (baseStart_3546557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3546557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3546557 prefixEnd_3546557 := by exact prefixLift 3546557
  have htrace : WordTrace (prefixWord ++ tailWord_3546557) baseStart_3546557 baseEnd_3546557 := by
    simpa [prefixWord, tailWord_3546557, baseEnd_3546557] using wordTrace_append hprefix tailTrace_3546557
  have hstable : (prefixWord ++ tailWord_3546557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546557).length < 2 ^ (prefixWord ++ tailWord_3546557).sum := by decide
  have hdescent : baseEnd_3546557 < baseStart_3546557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546591 : List Nat := [1, 1, 2, 3, 3, 1, 5, 2, 5]
def baseStart_3546591 : Nat := 118140960795 + 3546591 * 2 ^ 59
def prefixEnd_3546591 : Nat := 4983230072969 + 3 ^ 40 * 3546591 * 2
def baseEnd_3546591 : Nat := 202345096434448742233559

theorem tailTrace_3546591 : CollatzResearch.WordTrace tailWord_3546591 prefixEnd_3546591 202345096434448742233559 := by
  unfold tailWord_3546591
  simp only [CollatzResearch.WordTrace]
  refine ⟨129354800694313991364911627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86236533796209327576607751 129354800694313991364911627)
  ·
    refine ⟨194032201041470987047367441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129354800694313991364911627 194032201041470987047367441)
    ·
      refine ⟨145524150781103240285525581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194032201041470987047367441 145524150781103240285525581)
      ·
        refine ⟨54571556542913715107072093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145524150781103240285525581 54571556542913715107072093)
        ·
          refine ⟨20464333703592643165152035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54571556542913715107072093 20464333703592643165152035)
          ·
            refine ⟨30696500555388964747728053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20464333703592643165152035 30696500555388964747728053)
            ·
              refine ⟨2877796927067715445099505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30696500555388964747728053 2877796927067715445099505)
              ·
                refine ⟨2158347695300786583824629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2877796927067715445099505 2158347695300786583824629)
                ·
                  refine ⟨202345096434448742233559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2158347695300786583824629 202345096434448742233559)
                  ·
                    rfl

theorem cell23_3546591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5, 2, 5].length) (baseStart_3546591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3546591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3546591 prefixEnd_3546591 := by exact prefixLift 3546591
  have htrace : WordTrace (prefixWord ++ tailWord_3546591) baseStart_3546591 baseEnd_3546591 := by
    simpa [prefixWord, tailWord_3546591, baseEnd_3546591] using wordTrace_append hprefix tailTrace_3546591
  have hstable : (prefixWord ++ tailWord_3546591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546591).length < 2 ^ (prefixWord ++ tailWord_3546591).sum := by decide
  have hdescent : baseEnd_3546591 < baseStart_3546591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546602 : List Nat := [3, 1, 3, 1, 4, 2, 2, 1, 2, 2, 2]
def baseStart_3546602 : Nat := 118140960795 + 3546602 * 2 ^ 59
def prefixEnd_3546602 : Nat := 4983230072969 + 3 ^ 40 * 3546602 * 2
def baseEnd_3546602 : Nat := 1821111516197238137064481

theorem tailTrace_3546602 : CollatzResearch.WordTrace tailWord_3546602 prefixEnd_3546602 1821111516197238137064481 := by
  unfold tailWord_3546602
  simp only [CollatzResearch.WordTrace]
  refine ⟨32338800474318535060890515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86236801264849426829041373 32338800474318535060890515)
  ·
    refine ⟨48508200711477802591335773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32338800474318535060890515 48508200711477802591335773)
    ·
      refine ⟨18190575266804175971750915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48508200711477802591335773 18190575266804175971750915)
      ·
        refine ⟨27285862900206263957626373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18190575266804175971750915 27285862900206263957626373)
        ·
          refine ⟨5116099293788674492054945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27285862900206263957626373 5116099293788674492054945)
          ·
            refine ⟨3837074470341505869041209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5116099293788674492054945 3837074470341505869041209)
            ·
              refine ⟨2877805852756129401780907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3837074470341505869041209 2877805852756129401780907)
              ·
                refine ⟨4316708779134194102671361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2877805852756129401780907 4316708779134194102671361)
                ·
                  refine ⟨3237531584350645577003521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4316708779134194102671361 3237531584350645577003521)
                  ·
                    refine ⟨2428148688262984182752641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3237531584350645577003521 2428148688262984182752641)
                    ·
                      refine ⟨1821111516197238137064481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2428148688262984182752641 1821111516197238137064481)
                      ·
                        rfl

theorem cell23_3546602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2, 1, 2, 2, 2].length) (baseStart_3546602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3546602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3546602 prefixEnd_3546602 := by exact prefixLift 3546602
  have htrace : WordTrace (prefixWord ++ tailWord_3546602) baseStart_3546602 baseEnd_3546602 := by
    simpa [prefixWord, tailWord_3546602, baseEnd_3546602] using wordTrace_append hprefix tailTrace_3546602
  have hstable : (prefixWord ++ tailWord_3546602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546602).length < 2 ^ (prefixWord ++ tailWord_3546602).sum := by decide
  have hdescent : baseEnd_3546602 < baseStart_3546602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546607 : List Nat := [1, 1, 2, 1, 4, 1, 2, 1, 3, 3, 4]
def baseStart_3546607 : Nat := 118140960795 + 3546607 * 2 ^ 59
def prefixEnd_3546607 : Nat := 4983230072969 + 3 ^ 40 * 3546607 * 2
def baseEnd_3546607 : Nat := 1821114083600510617501957

theorem tailTrace_3546607 : CollatzResearch.WordTrace tailWord_3546607 prefixEnd_3546607 1821114083600510617501957 := by
  unfold tailWord_3546607
  simp only [CollatzResearch.WordTrace]
  refine ⟨129355384262256026097494075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86236922841504017398329383 129355384262256026097494075)
  ·
    refine ⟨194033076393384039146241113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129355384262256026097494075 194033076393384039146241113)
    ·
      refine ⟨145524807295038029359680835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194033076393384039146241113 145524807295038029359680835)
      ·
        refine ⟨218287210942557044039521253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145524807295038029359680835 218287210942557044039521253)
        ·
          refine ⟨40928852051729445757410235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 218287210942557044039521253 40928852051729445757410235)
          ·
            refine ⟨61393278077594168636115353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40928852051729445757410235 61393278077594168636115353)
            ·
              refine ⟨46044958558195626477086515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61393278077594168636115353 46044958558195626477086515)
              ·
                refine ⟨69067437837293439715629773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46044958558195626477086515 69067437837293439715629773)
                ·
                  refine ⟨25900289188985039893361165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69067437837293439715629773 25900289188985039893361165)
                  ·
                    refine ⟨9712608445869389960010437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25900289188985039893361165 9712608445869389960010437)
                    ·
                      refine ⟨1821114083600510617501957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9712608445869389960010437 1821114083600510617501957)
                      ·
                        rfl

theorem cell23_3546607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 3, 4].length) (baseStart_3546607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3546607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3546607 prefixEnd_3546607 := by exact prefixLift 3546607
  have htrace : WordTrace (prefixWord ++ tailWord_3546607) baseStart_3546607 baseEnd_3546607 := by
    simpa [prefixWord, tailWord_3546607, baseEnd_3546607] using wordTrace_append hprefix tailTrace_3546607
  have hstable : (prefixWord ++ tailWord_3546607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546607).length < 2 ^ (prefixWord ++ tailWord_3546607).sum := by decide
  have hdescent : baseEnd_3546607 < baseStart_3546607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546678 : List Nat := [5, 1, 2, 1, 3, 1, 1, 1, 1, 4, 3]
def baseStart_3546678 : Nat := 118140960795 + 3546678 * 2 ^ 59
def prefixEnd_3546678 : Nat := 4983230072969 + 3 ^ 40 * 3546678 * 2
def baseEnd_3546678 : Nat := 1821150540726979839714131

theorem tailTrace_3546678 : CollatzResearch.WordTrace tailWord_3546678 prefixEnd_3546678 1821150540726979839714131 := by
  unfold tailWord_3546678
  simp only [CollatzResearch.WordTrace]
  refine ⟨8084873365312425326458043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86238649229999203482219125 8084873365312425326458043)
  ·
    refine ⟨12127310047968637989687065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8084873365312425326458043 12127310047968637989687065)
    ·
      refine ⟨9095482535976478492265299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12127310047968637989687065 9095482535976478492265299)
      ·
        refine ⟨13643223803964717738397949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9095482535976478492265299 13643223803964717738397949)
        ·
          refine ⟨5116208926486769151899231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13643223803964717738397949 5116208926486769151899231)
          ·
            refine ⟨7674313389730153727848847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5116208926486769151899231 7674313389730153727848847)
            ·
              refine ⟨11511470084595230591773271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7674313389730153727848847 11511470084595230591773271)
              ·
                refine ⟨17267205126892845887659907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11511470084595230591773271 17267205126892845887659907)
                ·
                  refine ⟨25900807690339268831489861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17267205126892845887659907 25900807690339268831489861)
                  ·
                    refine ⟨4856401441938612905904349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25900807690339268831489861 4856401441938612905904349)
                    ·
                      refine ⟨1821150540726979839714131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4856401441938612905904349 1821150540726979839714131)
                      ·
                        rfl

theorem cell23_3546678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_3546678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3546678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3546678 prefixEnd_3546678 := by exact prefixLift 3546678
  have htrace : WordTrace (prefixWord ++ tailWord_3546678) baseStart_3546678 baseEnd_3546678 := by
    simpa [prefixWord, tailWord_3546678, baseEnd_3546678] using wordTrace_append hprefix tailTrace_3546678
  have hstable : (prefixWord ++ tailWord_3546678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546678).length < 2 ^ (prefixWord ++ tailWord_3546678).sum := by decide
  have hdescent : baseEnd_3546678 < baseStart_3546678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546685 : List Nat := [1, 4, 1, 3, 3, 1, 2, 3, 1, 4]
def baseStart_3546685 : Nat := 118140960795 + 3546685 * 2 ^ 59
def prefixEnd_3546685 : Nat := 4983230072969 + 3 ^ 40 * 3546685 * 2
def baseEnd_3546685 : Nat := 607051378363853770775533

theorem tailTrace_3546685 : CollatzResearch.WordTrace tailWord_3546685 prefixEnd_3546685 607051378363853770775533 := by
  unfold tailWord_3546685
  simp only [CollatzResearch.WordTrace]
  refine ⟨129358229155973445418833509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86238819437315630279222339 129358229155973445418833509)
  ·
    refine ⟨24254667966745021016031283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129358229155973445418833509 24254667966745021016031283)
    ·
      refine ⟨36382001950117531524046925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24254667966745021016031283 36382001950117531524046925)
      ·
        refine ⟨13643250731294074321517597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36382001950117531524046925 13643250731294074321517597)
        ·
          refine ⟨5116219024235277870569099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13643250731294074321517597 5116219024235277870569099)
          ·
            refine ⟨7674328536352916805853649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5116219024235277870569099 7674328536352916805853649)
            ·
              refine ⟨5755746402264687604390237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7674328536352916805853649 5755746402264687604390237)
              ·
                refine ⟨2158404900849257851646339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5755746402264687604390237 2158404900849257851646339)
                ·
                  refine ⟨3237607351273886777469509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2158404900849257851646339 3237607351273886777469509)
                  ·
                    refine ⟨607051378363853770775533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3237607351273886777469509 607051378363853770775533)
                    ·
                      rfl

theorem cell23_3546685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 3, 1, 4].length) (baseStart_3546685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3546685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3546685 prefixEnd_3546685 := by exact prefixLift 3546685
  have htrace : WordTrace (prefixWord ++ tailWord_3546685) baseStart_3546685 baseEnd_3546685 := by
    simpa [prefixWord, tailWord_3546685, baseEnd_3546685] using wordTrace_append hprefix tailTrace_3546685
  have hstable : (prefixWord ++ tailWord_3546685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546685).length < 2 ^ (prefixWord ++ tailWord_3546685).sum := by decide
  have hdescent : baseEnd_3546685 < baseStart_3546685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546708 : List Nat := [2, 4, 1, 1, 1, 2, 4, 1, 3, 1, 3]
def baseStart_3546708 : Nat := 118140960795 + 3546708 * 2 ^ 59
def prefixEnd_3546708 : Nat := 4983230072969 + 3 ^ 40 * 3546708 * 2
def baseEnd_3546708 : Nat := 1821165945146614722338993

theorem tailTrace_3546708 : CollatzResearch.WordTrace tailWord_3546708 prefixEnd_3546708 1821165945146614722338993 := by
  unfold tailWord_3546708
  simp only [CollatzResearch.WordTrace]
  refine ⟨64679534017445060173460389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86239378689926746897947185 64679534017445060173460389)
  ·
    refine ⟨12127412628270948782523823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64679534017445060173460389 12127412628270948782523823)
    ·
      refine ⟨18191118942406423173785735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12127412628270948782523823 18191118942406423173785735)
      ·
        refine ⟨27286678413609634760678603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18191118942406423173785735 27286678413609634760678603)
        ·
          refine ⟨40930017620414452141017905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27286678413609634760678603 40930017620414452141017905)
          ·
            refine ⟨30697513215310839105763429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40930017620414452141017905 30697513215310839105763429)
            ·
              refine ⟨5755783727870782332330643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30697513215310839105763429 5755783727870782332330643)
              ·
                refine ⟨8633675591806173498495965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5755783727870782332330643 8633675591806173498495965)
                ·
                  refine ⟨3237628346927315061935987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8633675591806173498495965 3237628346927315061935987)
                  ·
                    refine ⟨4856442520390972592903981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3237628346927315061935987 4856442520390972592903981)
                    ·
                      refine ⟨1821165945146614722338993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4856442520390972592903981 1821165945146614722338993)
                      ·
                        rfl

theorem cell23_3546708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 1, 3, 1, 3].length) (baseStart_3546708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3546708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3546708 prefixEnd_3546708 := by exact prefixLift 3546708
  have htrace : WordTrace (prefixWord ++ tailWord_3546708) baseStart_3546708 baseEnd_3546708 := by
    simpa [prefixWord, tailWord_3546708, baseEnd_3546708] using wordTrace_append hprefix tailTrace_3546708
  have hstable : (prefixWord ++ tailWord_3546708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546708).length < 2 ^ (prefixWord ++ tailWord_3546708).sum := by decide
  have hdescent : baseEnd_3546708 < baseStart_3546708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546714 : List Nat := [3, 1, 1, 2, 1, 1, 1, 3, 5, 1, 4]
def baseStart_3546714 : Nat := 118140960795 + 3546714 * 2 ^ 59
def prefixEnd_3546714 : Nat := 4983230072969 + 3 ^ 40 * 3546714 * 2
def baseEnd_3546714 : Nat := 1821169026030541698863965

theorem tailTrace_3546714 : CollatzResearch.WordTrace tailWord_3546714 prefixEnd_3546714 1821169026030541698863965 := by
  unfold tailWord_3546714
  simp only [CollatzResearch.WordTrace]
  refine ⟨32339821718217095842909799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86239524581912255581092797 32339821718217095842909799)
  ·
    refine ⟨48509732577325643764364699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32339821718217095842909799 48509732577325643764364699)
    ·
      refine ⟨72764598865988465646547049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48509732577325643764364699 72764598865988465646547049)
      ·
        refine ⟨54573449149491349234910287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72764598865988465646547049 54573449149491349234910287)
        ·
          refine ⟨81860173724237023852365431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54573449149491349234910287 81860173724237023852365431)
          ·
            refine ⟨122790260586355535778548147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81860173724237023852365431 122790260586355535778548147)
            ·
              refine ⟨184185390879533303667822221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122790260586355535778548147 184185390879533303667822221)
              ·
                refine ⟨69069521579824988875433333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 184185390879533303667822221 69069521579824988875433333)
                ·
                  refine ⟨6475267648108592707071875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69069521579824988875433333 6475267648108592707071875)
                  ·
                    refine ⟨9712901472162889060607813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6475267648108592707071875 9712901472162889060607813)
                    ·
                      refine ⟨1821169026030541698863965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9712901472162889060607813 1821169026030541698863965)
                      ·
                        rfl

theorem cell23_3546714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 5, 1, 4].length) (baseStart_3546714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3546714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3546714 prefixEnd_3546714 := by exact prefixLift 3546714
  have htrace : WordTrace (prefixWord ++ tailWord_3546714) baseStart_3546714 baseEnd_3546714 := by
    simpa [prefixWord, tailWord_3546714, baseEnd_3546714] using wordTrace_append hprefix tailTrace_3546714
  have hstable : (prefixWord ++ tailWord_3546714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546714).length < 2 ^ (prefixWord ++ tailWord_3546714).sum := by decide
  have hdescent : baseEnd_3546714 < baseStart_3546714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546728 : List Nat := [2, 1, 4, 3, 1, 2, 2, 2, 1, 5]
def baseStart_3546728 : Nat := 118140960795 + 3546728 * 2 ^ 59
def prefixEnd_3546728 : Nat := 4983230072969 + 3 ^ 40 * 3546728 * 2
def baseEnd_3546728 : Nat := 607058738253234881362967

theorem tailTrace_3546728 : CollatzResearch.WordTrace tailWord_3546728 prefixEnd_3546728 607058738253234881362967 := by
  unfold tailWord_3546728
  simp only [CollatzResearch.WordTrace]
  refine ⟨64679898747408831881324419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86239864996545109175099225 64679898747408831881324419)
  ·
    refine ⟨97019848121113247821986629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64679898747408831881324419 97019848121113247821986629)
    ·
      refine ⟨18191221522708733966622493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97019848121113247821986629 18191221522708733966622493)
      ·
        refine ⟨6821708071015775237483435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18191221522708733966622493 6821708071015775237483435)
        ·
          refine ⟨10232562106523662856225153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6821708071015775237483435 10232562106523662856225153)
          ·
            refine ⟨7674421579892747142168865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10232562106523662856225153 7674421579892747142168865)
            ·
              refine ⟨5755816184919560356626649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7674421579892747142168865 5755816184919560356626649)
              ·
                refine ⟨4316862138689670267469987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5755816184919560356626649 4316862138689670267469987)
                ·
                  refine ⟨6475293208034505401204981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4316862138689670267469987 6475293208034505401204981)
                  ·
                    refine ⟨607058738253234881362967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6475293208034505401204981 607058738253234881362967)
                    ·
                      rfl

theorem cell23_3546728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_3546728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3546728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3546728 prefixEnd_3546728 := by exact prefixLift 3546728
  have htrace : WordTrace (prefixWord ++ tailWord_3546728) baseStart_3546728 baseEnd_3546728 := by
    simpa [prefixWord, tailWord_3546728, baseEnd_3546728] using wordTrace_append hprefix tailTrace_3546728
  have hstable : (prefixWord ++ tailWord_3546728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546728).length < 2 ^ (prefixWord ++ tailWord_3546728).sum := by decide
  have hdescent : baseEnd_3546728 < baseStart_3546728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546742 : List Nat := [5, 1, 1, 2, 2, 1, 3, 3, 1, 1, 3]
def baseStart_3546742 : Nat := 118140960795 + 3546742 * 2 ^ 59
def prefixEnd_3546742 : Nat := 4983230072969 + 3 ^ 40 * 3546742 * 2
def baseEnd_3546742 : Nat := 1821183403488867589313837

theorem tailTrace_3546742 : CollatzResearch.WordTrace tailWord_3546742 prefixEnd_3546742 1821183403488867589313837 := by
  unfold tailWord_3546742
  simp only [CollatzResearch.WordTrace]
  refine ⟨8085019257297934009603655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86240205411177962769105653 8085019257297934009603655)
  ·
    refine ⟨12127528885946901014405483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8085019257297934009603655 12127528885946901014405483)
    ·
      refine ⟨18191293328920351521608225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12127528885946901014405483 18191293328920351521608225)
      ·
        refine ⟨13643469996690263641206169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18191293328920351521608225 13643469996690263641206169)
        ·
          refine ⟨10232602497517697730904627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13643469996690263641206169 10232602497517697730904627)
          ·
            refine ⟨15348903746276546596356941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10232602497517697730904627 15348903746276546596356941)
            ·
              refine ⟨5755838904853704973633853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15348903746276546596356941 5755838904853704973633853)
              ·
                refine ⟨2158439589320139365112695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5755838904853704973633853 2158439589320139365112695)
                ·
                  refine ⟨3237659383980209047669043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2158439589320139365112695 3237659383980209047669043)
                  ·
                    refine ⟨4856489075970313571503565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3237659383980209047669043 4856489075970313571503565)
                    ·
                      refine ⟨1821183403488867589313837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4856489075970313571503565 1821183403488867589313837)
                      ·
                        rfl

theorem cell23_3546742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_3546742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3546742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3546742 prefixEnd_3546742 := by exact prefixLift 3546742
  have htrace : WordTrace (prefixWord ++ tailWord_3546742) baseStart_3546742 baseEnd_3546742 := by
    simpa [prefixWord, tailWord_3546742, baseEnd_3546742] using wordTrace_append hprefix tailTrace_3546742
  have hstable : (prefixWord ++ tailWord_3546742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546742).length < 2 ^ (prefixWord ++ tailWord_3546742).sum := by decide
  have hdescent : baseEnd_3546742 < baseStart_3546742 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546775 : List Nat := [1, 1, 3, 3, 2, 4, 2, 1, 2, 4]
def baseStart_3546775 : Nat := 118140960795 + 3546775 * 2 ^ 59
def prefixEnd_3546775 : Nat := 4983230072969 + 3 ^ 40 * 3546775 * 2
def baseEnd_3546775 : Nat := 607066782783488653400395

theorem tailTrace_3546775 : CollatzResearch.WordTrace tailWord_3546775 prefixEnd_3546775 607066782783488653400395 := by
  unfold tailWord_3546775
  simp only [CollatzResearch.WordTrace]
  refine ⟨129361511725647390789609779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86241007817098260526406519 129361511725647390789609779)
  ·
    refine ⟨194042267588471086184414669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129361511725647390789609779 194042267588471086184414669)
    ·
      refine ⟨72765850345676657319155501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194042267588471086184414669 72765850345676657319155501)
      ·
        refine ⟨27287193879628746494683313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72765850345676657319155501 27287193879628746494683313)
        ·
          refine ⟨20465395409721559871012485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27287193879628746494683313 20465395409721559871012485)
          ·
            refine ⟨3837261639322792475814841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20465395409721559871012485 3837261639322792475814841)
            ·
              refine ⟨2877946229492094356861131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3837261639322792475814841 2877946229492094356861131)
              ·
                refine ⟨4316919344238141535291697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2877946229492094356861131 4316919344238141535291697)
                ·
                  refine ⟨3237689508178606151468773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4316919344238141535291697 3237689508178606151468773)
                  ·
                    refine ⟨607066782783488653400395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3237689508178606151468773 607066782783488653400395)
                    ·
                      rfl

theorem cell23_3546775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2, 1, 2, 4].length) (baseStart_3546775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3546775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3546775 prefixEnd_3546775 := by exact prefixLift 3546775
  have htrace : WordTrace (prefixWord ++ tailWord_3546775) baseStart_3546775 baseEnd_3546775 := by
    simpa [prefixWord, tailWord_3546775, baseEnd_3546775] using wordTrace_append hprefix tailTrace_3546775
  have hstable : (prefixWord ++ tailWord_3546775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546775).length < 2 ^ (prefixWord ++ tailWord_3546775).sum := by decide
  have hdescent : baseEnd_3546775 < baseStart_3546775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546781 : List Nat := [1, 4, 2, 1, 1, 1, 1, 5, 1, 3, 3]
def baseStart_3546781 : Nat := 118140960795 + 3546781 * 2 ^ 59
def prefixEnd_3546781 : Nat := 4983230072969 + 3 ^ 40 * 3546781 * 2
def baseEnd_3546781 : Nat := 1821203429234392936726157

theorem tailTrace_3546781 : CollatzResearch.WordTrace tailWord_3546781 prefixEnd_3546781 1821203429234392936726157 := by
  unfold tailWord_3546781
  simp only [CollatzResearch.WordTrace]
  refine ⟨129361730563625653814328197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86241153709083769209552131 129361730563625653814328197)
  ·
    refine ⟨24255324480679810090186537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129361730563625653814328197 24255324480679810090186537)
    ·
      refine ⟨18191493360509857567639903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24255324480679810090186537 18191493360509857567639903)
      ·
        refine ⟨27287240040764786351459855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18191493360509857567639903 27287240040764786351459855)
        ·
          refine ⟨40930860061147179527189783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27287240040764786351459855 40930860061147179527189783)
          ·
            refine ⟨61396290091720769290784675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40930860061147179527189783 61396290091720769290784675)
            ·
              refine ⟨92094435137581153936177013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61396290091720769290784675 92094435137581153936177013)
              ·
                refine ⟨8633853294148233181516595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92094435137581153936177013 8633853294148233181516595)
                ·
                  refine ⟨12950779941222349772274893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8633853294148233181516595 12950779941222349772274893)
                  ·
                    refine ⟨4856542477958381164603085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12950779941222349772274893 4856542477958381164603085)
                    ·
                      refine ⟨1821203429234392936726157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4856542477958381164603085 1821203429234392936726157)
                      ·
                        rfl

theorem cell23_3546781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_3546781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3546781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3546781 prefixEnd_3546781 := by exact prefixLift 3546781
  have htrace : WordTrace (prefixWord ++ tailWord_3546781) baseStart_3546781 baseEnd_3546781 := by
    simpa [prefixWord, tailWord_3546781, baseEnd_3546781] using wordTrace_append hprefix tailTrace_3546781
  have hstable : (prefixWord ++ tailWord_3546781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546781).length < 2 ^ (prefixWord ++ tailWord_3546781).sum := by decide
  have hdescent : baseEnd_3546781 < baseStart_3546781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546785 : List Nat := [1, 2, 3, 3, 2, 3, 1, 2, 1, 2, 3]
def baseStart_3546785 : Nat := 118140960795 + 3546785 * 2 ^ 59
def prefixEnd_3546785 : Nat := 4983230072969 + 3 ^ 40 * 3546785 * 2
def baseEnd_3546785 : Nat := 1821205483157010921076139

theorem tailTrace_3546785 : CollatzResearch.WordTrace tailWord_3546785 prefixEnd_3546785 1821205483157010921076139 := by
  unfold tailWord_3546785
  simp only [CollatzResearch.WordTrace]
  refine ⟨129361876455611162497473809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86241250970407441664982539 129361876455611162497473809)
  ·
    refine ⟨97021407341708371873105357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129361876455611162497473809 97021407341708371873105357)
    ·
      refine ⟨36383027753140639452414509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97021407341708371873105357 36383027753140639452414509)
      ·
        refine ⟨13643635407427739794655441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36383027753140639452414509 13643635407427739794655441)
        ·
          refine ⟨10232726555570804845991581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13643635407427739794655441 10232726555570804845991581)
          ·
            refine ⟨3837272458339051817246843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10232726555570804845991581 3837272458339051817246843)
            ·
              refine ⟨5755908687508577725870265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3837272458339051817246843 5755908687508577725870265)
              ·
                refine ⟨4316931515631433294402699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5755908687508577725870265 4316931515631433294402699)
                ·
                  refine ⟨6475397273447149941604049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4316931515631433294402699 6475397273447149941604049)
                  ·
                    refine ⟨4856547955085362456203037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6475397273447149941604049 4856547955085362456203037)
                    ·
                      refine ⟨1821205483157010921076139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4856547955085362456203037 1821205483157010921076139)
                      ·
                        rfl

theorem cell23_3546785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_3546785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3546785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3546785 prefixEnd_3546785 := by exact prefixLift 3546785
  have htrace : WordTrace (prefixWord ++ tailWord_3546785) baseStart_3546785 baseEnd_3546785 := by
    simpa [prefixWord, tailWord_3546785, baseEnd_3546785] using wordTrace_append hprefix tailTrace_3546785
  have hstable : (prefixWord ++ tailWord_3546785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546785).length < 2 ^ (prefixWord ++ tailWord_3546785).sum := by decide
  have hdescent : baseEnd_3546785 < baseStart_3546785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546808 : List Nat := [2, 1, 2, 1, 2, 1, 1, 7, 1, 3, 2]
def baseStart_3546808 : Nat := 118140960795 + 3546808 * 2 ^ 59
def prefixEnd_3546808 : Nat := 4983230072969 + 3 ^ 40 * 3546808 * 2
def baseEnd_3546808 : Nat := 1821217293212064331088533

theorem tailTrace_3546808 : CollatzResearch.WordTrace tailWord_3546808 prefixEnd_3546808 1821217293212064331088533 := by
  unfold tailWord_3546808
  simp only [CollatzResearch.WordTrace]
  refine ⟨64681357667263918712780539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86241810223018558283707385 64681357667263918712780539)
  ·
    refine ⟨97022036500895878069170809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64681357667263918712780539 97022036500895878069170809)
    ·
      refine ⟨72766527375671908551878107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97022036500895878069170809 72766527375671908551878107)
      ·
        refine ⟨109149791063507862827817161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72766527375671908551878107 109149791063507862827817161)
        ·
          refine ⟨81862343297630897120862871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109149791063507862827817161 81862343297630897120862871)
          ·
            refine ⟨122793514946446345681294307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81862343297630897120862871 122793514946446345681294307)
            ·
              refine ⟨184190272419669518521941461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122793514946446345681294307 184190272419669518521941461)
              ·
                refine ⟨4316959509836004340358003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 184190272419669518521941461 4316959509836004340358003)
                ·
                  refine ⟨6475439264754006510537005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4316959509836004340358003 6475439264754006510537005)
                  ·
                    refine ⟨2428289724282752441451377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6475439264754006510537005 2428289724282752441451377)
                    ·
                      refine ⟨1821217293212064331088533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2428289724282752441451377 1821217293212064331088533)
                      ·
                        rfl

theorem cell23_3546808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 7, 1, 3, 2].length) (baseStart_3546808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3546808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3546808 prefixEnd_3546808 := by exact prefixLift 3546808
  have htrace : WordTrace (prefixWord ++ tailWord_3546808) baseStart_3546808 baseEnd_3546808 := by
    simpa [prefixWord, tailWord_3546808, baseEnd_3546808] using wordTrace_append hprefix tailTrace_3546808
  have hstable : (prefixWord ++ tailWord_3546808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546808).length < 2 ^ (prefixWord ++ tailWord_3546808).sum := by decide
  have hdescent : baseEnd_3546808 < baseStart_3546808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546871 : List Nat := [1, 1, 3, 1, 1, 1, 5, 2, 2, 3, 3]
def baseStart_3546871 : Nat := 118140960795 + 3546871 * 2 ^ 59
def prefixEnd_3546871 : Nat := 4983230072969 + 3 ^ 40 * 3546871 * 2
def baseEnd_3546871 : Nat := 1821249642493297584600743

theorem tailTrace_3546871 : CollatzResearch.WordTrace tailWord_3546871 prefixEnd_3546871 1821249642493297584600743 := by
  unfold tailWord_3546871
  simp only [CollatzResearch.WordTrace]
  refine ⟨129365013133299599185104467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86243342088866399456736311 129365013133299599185104467)
  ·
    refine ⟨194047519699949398777656701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129365013133299599185104467 194047519699949398777656701)
    ·
      refine ⟨72767819887481024541621263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194047519699949398777656701 72767819887481024541621263)
      ·
        refine ⟨109151729831221536812431895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72767819887481024541621263 109151729831221536812431895)
        ·
          refine ⟨163727594746832305218647843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109151729831221536812431895 163727594746832305218647843)
          ·
            refine ⟨245591392120248457827971765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163727594746832305218647843 245591392120248457827971765)
            ·
              refine ⟨23024193011273292921372353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 245591392120248457827971765 23024193011273292921372353)
              ·
                refine ⟨17268144758454969691029265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23024193011273292921372353 17268144758454969691029265)
                ·
                  refine ⟨12951108568841227268271949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17268144758454969691029265 12951108568841227268271949)
                  ·
                    refine ⟨4856665713315460225601981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12951108568841227268271949 4856665713315460225601981)
                    ·
                      refine ⟨1821249642493297584600743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4856665713315460225601981 1821249642493297584600743)
                      ·
                        rfl

theorem cell23_3546871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 2, 3, 3].length) (baseStart_3546871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3546871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3546871 prefixEnd_3546871 := by exact prefixLift 3546871
  have htrace : WordTrace (prefixWord ++ tailWord_3546871) baseStart_3546871 baseEnd_3546871 := by
    simpa [prefixWord, tailWord_3546871, baseEnd_3546871] using wordTrace_append hprefix tailTrace_3546871
  have hstable : (prefixWord ++ tailWord_3546871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546871).length < 2 ^ (prefixWord ++ tailWord_3546871).sum := by decide
  have hdescent : baseEnd_3546871 < baseStart_3546871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546893 : List Nat := [1, 7, 2, 1, 1, 1, 2, 2, 1, 3, 2]
def baseStart_3546893 : Nat := 118140960795 + 3546893 * 2 ^ 59
def prefixEnd_3546893 : Nat := 4983230072969 + 3 ^ 40 * 3546893 * 2
def baseEnd_3546893 : Nat := 1821260939067696498525643

theorem tailTrace_3546893 : CollatzResearch.WordTrace tailWord_3546893 prefixEnd_3546893 1821260939067696498525643 := by
  unfold tailWord_3546893
  simp only [CollatzResearch.WordTrace]
  refine ⟨129365815539219896942405333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86243877026146597961603555 129365815539219896942405333)
  ·
    refine ⟨3032011301700466334587625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 129365815539219896942405333 3032011301700466334587625)
    ·
      refine ⟨2274008476275349750940719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3032011301700466334587625 2274008476275349750940719)
      ·
        refine ⟨3411012714413024626411079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2274008476275349750940719 3411012714413024626411079)
        ·
          refine ⟨5116519071619536939616619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3411012714413024626411079 5116519071619536939616619)
          ·
            refine ⟨7674778607429305409424929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5116519071619536939616619 7674778607429305409424929)
            ·
              refine ⟨5756083955571979057068697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7674778607429305409424929 5756083955571979057068697)
              ·
                refine ⟨4317062966678984292801523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5756083955571979057068697 4317062966678984292801523)
                ·
                  refine ⟨6475594450018476439202285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4317062966678984292801523 6475594450018476439202285)
                  ·
                    refine ⟨2428347918756928664700857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6475594450018476439202285 2428347918756928664700857)
                    ·
                      refine ⟨1821260939067696498525643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2428347918756928664700857 1821260939067696498525643)
                      ·
                        rfl

theorem cell23_3546893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_3546893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3546893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3546893 prefixEnd_3546893 := by exact prefixLift 3546893
  have htrace : WordTrace (prefixWord ++ tailWord_3546893) baseStart_3546893 baseEnd_3546893 := by
    simpa [prefixWord, tailWord_3546893, baseEnd_3546893] using wordTrace_append hprefix tailTrace_3546893
  have hstable : (prefixWord ++ tailWord_3546893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546893).length < 2 ^ (prefixWord ++ tailWord_3546893).sum := by decide
  have hdescent : baseEnd_3546893 < baseStart_3546893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546911 : List Nat := [1, 1, 2, 4, 2, 1, 1, 3, 1, 3, 4]
def baseStart_3546911 : Nat := 118140960795 + 3546911 * 2 ^ 59
def prefixEnd_3546911 : Nat := 4983230072969 + 3 ^ 40 * 3546911 * 2
def baseEnd_3546911 : Nat := 1821270181719477428100559

theorem tailTrace_3546911 : CollatzResearch.WordTrace tailWord_3546911 prefixEnd_3546911 1821270181719477428100559 := by
  unfold tailWord_3546911
  simp only [CollatzResearch.WordTrace]
  refine ⟨129366472053154686016560587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86244314702103124011040391 129366472053154686016560587)
  ·
    refine ⟨194049708079732029024840881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129366472053154686016560587 194049708079732029024840881)
    ·
      refine ⟨145537281059799021768630661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194049708079732029024840881 145537281059799021768630661)
      ·
        refine ⟨27288240198712316581618249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145537281059799021768630661 27288240198712316581618249)
        ·
          refine ⟨20466180149034237436213687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27288240198712316581618249 20466180149034237436213687)
          ·
            refine ⟨30699270223551356154320531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20466180149034237436213687 30699270223551356154320531)
            ·
              refine ⟨46048905335327034231480797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30699270223551356154320531 46048905335327034231480797)
              ·
                refine ⟨17268339500747637836805299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46048905335327034231480797 17268339500747637836805299)
                ·
                  refine ⟨25902509251121456755207949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17268339500747637836805299 25902509251121456755207949)
                  ·
                    refine ⟨9713440969170546283202981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25902509251121456755207949 9713440969170546283202981)
                    ·
                      refine ⟨1821270181719477428100559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9713440969170546283202981 1821270181719477428100559)
                      ·
                        rfl

theorem cell23_3546911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_3546911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3546911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3546911 prefixEnd_3546911 := by exact prefixLift 3546911
  have htrace : WordTrace (prefixWord ++ tailWord_3546911) baseStart_3546911 baseEnd_3546911 := by
    simpa [prefixWord, tailWord_3546911, baseEnd_3546911] using wordTrace_append hprefix tailTrace_3546911
  have hstable : (prefixWord ++ tailWord_3546911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546911).length < 2 ^ (prefixWord ++ tailWord_3546911).sum := by decide
  have hdescent : baseEnd_3546911 < baseStart_3546911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3546965 : List Nat := [1, 3, 2, 2, 2, 3, 2, 1, 2, 2, 3]
def baseStart_3546965 : Nat := 118140960795 + 3546965 * 2 ^ 59
def prefixEnd_3546965 : Nat := 4983230072969 + 3 ^ 40 * 3546965 * 2
def baseEnd_3546965 : Nat := 1821297909674820216825311

theorem tailTrace_3546965 : CollatzResearch.WordTrace tailWord_3546965 prefixEnd_3546965 1821297909674820216825311 := by
  unfold tailWord_3546965
  simp only [CollatzResearch.WordTrace]
  refine ⟨129368441594959053239026349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86245627729972702159350899 129368441594959053239026349)
  ·
    refine ⟨48513165598109644964634881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129368441594959053239026349 48513165598109644964634881)
    ·
      refine ⟨36384874198582233723476161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48513165598109644964634881 36384874198582233723476161)
      ·
        refine ⟨27288655648936675292607121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36384874198582233723476161 27288655648936675292607121)
        ·
          refine ⟨20466491736702506469455341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27288655648936675292607121 20466491736702506469455341)
          ·
            refine ⟨7674934401263439926045753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20466491736702506469455341 7674934401263439926045753)
            ·
              refine ⟨5756200800947579944534315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7674934401263439926045753 5756200800947579944534315)
              ·
                refine ⟨8634301201421369916801473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5756200800947579944534315 8634301201421369916801473)
                ·
                  refine ⟨6475725901066027437601105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8634301201421369916801473 6475725901066027437601105)
                  ·
                    refine ⟨4856794425799520578200829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6475725901066027437601105 4856794425799520578200829)
                    ·
                      refine ⟨1821297909674820216825311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4856794425799520578200829 1821297909674820216825311)
                      ·
                        rfl

theorem cell23_3546965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_3546965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3546965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3546965 prefixEnd_3546965 := by exact prefixLift 3546965
  have htrace : WordTrace (prefixWord ++ tailWord_3546965) baseStart_3546965 baseEnd_3546965 := by
    simpa [prefixWord, tailWord_3546965, baseEnd_3546965] using wordTrace_append hprefix tailTrace_3546965
  have hstable : (prefixWord ++ tailWord_3546965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3546965).length < 2 ^ (prefixWord ++ tailWord_3546965).sum := by decide
  have hdescent : baseEnd_3546965 < baseStart_3546965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3546965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547032 : List Nat := [2, 1, 2, 6, 1, 1, 1, 3, 1, 5]
def baseStart_3547032 : Nat := 118140960795 + 3547032 * 2 ^ 59
def prefixEnd_3547032 : Nat := 4983230072969 + 3 ^ 40 * 3547032 * 2
def baseEnd_3547032 : Nat := 607110770959557151562501

theorem tailTrace_3547032 : CollatzResearch.WordTrace tailWord_3547032 prefixEnd_3547032 607110770959557151562501 := by
  unfold tailWord_3547032
  simp only [CollatzResearch.WordTrace]
  refine ⟨64685442642858161840857675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86247256857144215787810233 64685442642858161840857675)
  ·
    refine ⟨97028163964287242761286513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64685442642858161840857675 97028163964287242761286513)
    ·
      refine ⟨72771122973215432070964885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97028163964287242761286513 72771122973215432070964885)
      ·
        refine ⟨3411146389369473378326479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 72771122973215432070964885 3411146389369473378326479)
        ·
          refine ⟨5116719584054210067489719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3411146389369473378326479 5116719584054210067489719)
          ·
            refine ⟨7675079376081315101234579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5116719584054210067489719 7675079376081315101234579)
            ·
              refine ⟨11512619064121972651851869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7675079376081315101234579 11512619064121972651851869)
              ·
                refine ⟨4317232149045739744444451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11512619064121972651851869 4317232149045739744444451)
                ·
                  refine ⟨6475848223568609616666677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4317232149045739744444451 6475848223568609616666677)
                  ·
                    refine ⟨607110770959557151562501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6475848223568609616666677 607110770959557151562501)
                    ·
                      rfl

theorem cell23_3547032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 3, 1, 5].length) (baseStart_3547032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3547032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3547032 prefixEnd_3547032 := by exact prefixLift 3547032
  have htrace : WordTrace (prefixWord ++ tailWord_3547032) baseStart_3547032 baseEnd_3547032 := by
    simpa [prefixWord, tailWord_3547032, baseEnd_3547032] using wordTrace_append hprefix tailTrace_3547032
  have hstable : (prefixWord ++ tailWord_3547032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547032).length < 2 ^ (prefixWord ++ tailWord_3547032).sum := by decide
  have hdescent : baseEnd_3547032 < baseStart_3547032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547108 : List Nat := [2, 3, 1, 1, 1, 1, 4, 1, 2, 3, 4]
def baseStart_3547108 : Nat := 118140960795 + 3547108 * 2 ^ 59
def prefixEnd_3547108 : Nat := 4983230072969 + 3 ^ 40 * 3547108 * 2
def baseEnd_3547108 : Nat := 1821371337408413157337153

theorem tailTrace_3547108 : CollatzResearch.WordTrace tailWord_3547108 prefixEnd_3547108 1821371337408413157337153 := by
  unfold tailWord_3547108
  simp only [CollatzResearch.WordTrace]
  refine ⟨64686828616720494330740989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86249104822293992440987985 64686828616720494330740989)
  ·
    refine ⟨24257560731270185374027871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64686828616720494330740989 24257560731270185374027871)
    ·
      refine ⟨36386341096905278061041807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24257560731270185374027871 36386341096905278061041807)
      ·
        refine ⟨54579511645357917091562711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36386341096905278061041807 54579511645357917091562711)
        ·
          refine ⟨81869267468036875637344067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54579511645357917091562711 81869267468036875637344067)
          ·
            refine ⟨122803901202055313456016101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81869267468036875637344067 122803901202055313456016101)
            ·
              refine ⟨23025731475385371273003019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122803901202055313456016101 23025731475385371273003019)
              ·
                refine ⟨34538597213078056909504529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23025731475385371273003019 34538597213078056909504529)
                ·
                  refine ⟨25903947909808542682128397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34538597213078056909504529 25903947909808542682128397)
                  ·
                    refine ⟨9713980466178203505798149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25903947909808542682128397 9713980466178203505798149)
                    ·
                      refine ⟨1821371337408413157337153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9713980466178203505798149 1821371337408413157337153)
                      ·
                        rfl

theorem cell23_3547108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_3547108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3547108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3547108 prefixEnd_3547108 := by exact prefixLift 3547108
  have htrace : WordTrace (prefixWord ++ tailWord_3547108) baseStart_3547108 baseEnd_3547108 := by
    simpa [prefixWord, tailWord_3547108, baseEnd_3547108] using wordTrace_append hprefix tailTrace_3547108
  have hstable : (prefixWord ++ tailWord_3547108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547108).length < 2 ^ (prefixWord ++ tailWord_3547108).sum := by decide
  have hdescent : baseEnd_3547108 < baseStart_3547108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547128 : List Nat := [2, 1, 2, 1, 1, 3, 3, 2, 2, 1, 5]
def baseStart_3547128 : Nat := 118140960795 + 3547128 * 2 ^ 59
def prefixEnd_3547128 : Nat := 4983230072969 + 3 ^ 40 * 3547128 * 2
def baseEnd_3547128 : Nat := 1821381607021503079087061

theorem tailTrace_3547128 : CollatzResearch.WordTrace tailWord_3547128 prefixEnd_3547128 1821381607021503079087061 := by
  unfold tailWord_3547128
  simp only [CollatzResearch.WordTrace]
  refine ⟨64687193346684266038605019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86249591128912354718140025 64687193346684266038605019)
  ·
    refine ⟨97030790020026399057907529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64687193346684266038605019 97030790020026399057907529)
    ·
      refine ⟨72773092515019799293430647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97030790020026399057907529 72773092515019799293430647)
      ·
        refine ⟨109159638772529698940145971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72773092515019799293430647 109159638772529698940145971)
        ·
          refine ⟨163739458158794548410218957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109159638772529698940145971 163739458158794548410218957)
          ·
            refine ⟨61402296809547955653832109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163739458158794548410218957 61402296809547955653832109)
            ·
              refine ⟨23025861303580483370187041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61402296809547955653832109 23025861303580483370187041)
              ·
                refine ⟨17269395977685362527640281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23025861303580483370187041 17269395977685362527640281)
                ·
                  refine ⟨12952046983264021895730211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17269395977685362527640281 12952046983264021895730211)
                  ·
                    refine ⟨19428070474896032843595317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12952046983264021895730211 19428070474896032843595317)
                    ·
                      refine ⟨1821381607021503079087061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19428070474896032843595317 1821381607021503079087061)
                      ·
                        rfl

theorem cell23_3547128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 2, 1, 5].length) (baseStart_3547128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3547128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3547128 prefixEnd_3547128 := by exact prefixLift 3547128
  have htrace : WordTrace (prefixWord ++ tailWord_3547128) baseStart_3547128 baseEnd_3547128 := by
    simpa [prefixWord, tailWord_3547128, baseEnd_3547128] using wordTrace_append hprefix tailTrace_3547128
  have hstable : (prefixWord ++ tailWord_3547128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547128).length < 2 ^ (prefixWord ++ tailWord_3547128).sum := by decide
  have hdescent : baseEnd_3547128 < baseStart_3547128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547129 : List Nat := [1, 2, 1, 3, 1, 6, 1, 2, 1, 3, 2]
def baseStart_3547129 : Nat := 118140960795 + 3547129 * 2 ^ 59
def prefixEnd_3547129 : Nat := 4983230072969 + 3 ^ 40 * 3547129 * 2
def baseEnd_3547129 : Nat := 1821382120502157575174557

theorem tailTrace_3547129 : CollatzResearch.WordTrace tailWord_3547129 prefixEnd_3547129 1821382120502157575174557 := by
  unfold tailWord_3547129
  simp only [CollatzResearch.WordTrace]
  refine ⟨129374423166364909247996441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86249615444243272831997627 129374423166364909247996441)
  ·
    refine ⟨97030817374773681935997331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129374423166364909247996441 97030817374773681935997331)
    ·
      refine ⟨145546226062160522903995997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97030817374773681935997331 145546226062160522903995997)
      ·
        refine ⟨54579834773310196088998499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145546226062160522903995997 54579834773310196088998499)
        ·
          refine ⟨81869752159965294133497749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54579834773310196088998499 81869752159965294133497749)
          ·
            refine ⟨3837644632498373162507707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 81869752159965294133497749 3837644632498373162507707)
            ·
              refine ⟨5756466948747559743761561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3837644632498373162507707 5756466948747559743761561)
              ·
                refine ⟨4317350211560669807821171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5756466948747559743761561 4317350211560669807821171)
                ·
                  refine ⟨6476025317341004711731757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4317350211560669807821171 6476025317341004711731757)
                  ·
                    refine ⟨2428509494002876766899409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6476025317341004711731757 2428509494002876766899409)
                    ·
                      refine ⟨1821382120502157575174557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2428509494002876766899409 1821382120502157575174557)
                      ·
                        rfl

theorem cell23_3547129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 2, 1, 3, 2].length) (baseStart_3547129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3547129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3547129 prefixEnd_3547129 := by exact prefixLift 3547129
  have htrace : WordTrace (prefixWord ++ tailWord_3547129) baseStart_3547129 baseEnd_3547129 := by
    simpa [prefixWord, tailWord_3547129, baseEnd_3547129] using wordTrace_append hprefix tailTrace_3547129
  have hstable : (prefixWord ++ tailWord_3547129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547129).length < 2 ^ (prefixWord ++ tailWord_3547129).sum := by decide
  have hdescent : baseEnd_3547129 < baseStart_3547129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547146 : List Nat := [3, 1, 2, 2, 4, 1, 3, 1, 1, 3, 2]
def baseStart_3547146 : Nat := 118140960795 + 3547146 * 2 ^ 59
def prefixEnd_3547146 : Nat := 4983230072969 + 3 ^ 40 * 3547146 * 2
def baseEnd_3547146 : Nat := 1821390849673284008661979

theorem tailTrace_3547146 : CollatzResearch.WordTrace tailWord_3547146 prefixEnd_3547146 1821390849673284008661979 := by
  unfold tailWord_3547146
  simp only [CollatzResearch.WordTrace]
  refine ⟨32343760801825830287841323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86250028804868880767576861 32343760801825830287841323)
  ·
    refine ⟨48515641202738745431761985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32343760801825830287841323 48515641202738745431761985)
    ·
      refine ⟨36386730902054059073821489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48515641202738745431761985 36386730902054059073821489)
      ·
        refine ⟨27290048176540544305366117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36386730902054059073821489 27290048176540544305366117)
        ·
          refine ⟨5116884033101352057256147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27290048176540544305366117 5116884033101352057256147)
          ·
            refine ⟨7675326049652028085884221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5116884033101352057256147 7675326049652028085884221)
            ·
              refine ⟨2878247268619510532206583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7675326049652028085884221 2878247268619510532206583)
              ·
                refine ⟨4317370902929265798309875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2878247268619510532206583 4317370902929265798309875)
                ·
                  refine ⟨6476056354393898697464813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4317370902929265798309875 6476056354393898697464813)
                  ·
                    refine ⟨2428521132897712011549305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6476056354393898697464813 2428521132897712011549305)
                    ·
                      refine ⟨1821390849673284008661979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2428521132897712011549305 1821390849673284008661979)
                      ·
                        rfl

theorem cell23_3547146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3, 1, 1, 3, 2].length) (baseStart_3547146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3547146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3547146 prefixEnd_3547146 := by exact prefixLift 3547146
  have htrace : WordTrace (prefixWord ++ tailWord_3547146) baseStart_3547146 baseEnd_3547146 := by
    simpa [prefixWord, tailWord_3547146, baseEnd_3547146] using wordTrace_append hprefix tailTrace_3547146
  have hstable : (prefixWord ++ tailWord_3547146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547146).length < 2 ^ (prefixWord ++ tailWord_3547146).sum := by decide
  have hdescent : baseEnd_3547146 < baseStart_3547146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547172 : List Nat := [2, 3, 1, 4, 2, 1, 1, 1, 2, 2, 4]
def baseStart_3547172 : Nat := 118140960795 + 3547172 * 2 ^ 59
def prefixEnd_3547172 : Nat := 4983230072969 + 3 ^ 40 * 3547172 * 2
def baseEnd_3547172 : Nat := 1821404200170300906936859

theorem tailTrace_3547172 : CollatzResearch.WordTrace tailWord_3547172 prefixEnd_3547172 1821404200170300906936859 := by
  unfold tailWord_3547172
  simp only [CollatzResearch.WordTrace]
  refine ⟨64687995752604563795905885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86250661003472751727874513 64687995752604563795905885)
  ·
    refine ⟨24257998407226711423464707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64687995752604563795905885 24257998407226711423464707)
    ·
      refine ⟨36386997610840067135197061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24257998407226711423464707 36386997610840067135197061)
      ·
        refine ⟨6822562052032512587849449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36386997610840067135197061 6822562052032512587849449)
        ·
          refine ⟨5116921539024384440887087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6822562052032512587849449 5116921539024384440887087)
          ·
            refine ⟨7675382308536576661330631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5116921539024384440887087 7675382308536576661330631)
            ·
              refine ⟨11513073462804864991995947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7675382308536576661330631 11513073462804864991995947)
              ·
                refine ⟨17269610194207297487993921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11513073462804864991995947 17269610194207297487993921)
                ·
                  refine ⟨12952207645655473115995441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17269610194207297487993921 12952207645655473115995441)
                  ·
                    refine ⟨9714155734241604836996581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12952207645655473115995441 9714155734241604836996581)
                    ·
                      refine ⟨1821404200170300906936859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9714155734241604836996581 1821404200170300906936859)
                      ·
                        rfl

theorem cell23_3547172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_3547172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3547172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3547172 prefixEnd_3547172 := by exact prefixLift 3547172
  have htrace : WordTrace (prefixWord ++ tailWord_3547172) baseStart_3547172 baseEnd_3547172 := by
    simpa [prefixWord, tailWord_3547172, baseEnd_3547172] using wordTrace_append hprefix tailTrace_3547172
  have hstable : (prefixWord ++ tailWord_3547172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547172).length < 2 ^ (prefixWord ++ tailWord_3547172).sum := by decide
  have hdescent : baseEnd_3547172 < baseStart_3547172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547176 : List Nat := [2, 1, 5, 3, 1, 1, 2, 1, 1, 4, 2]
def baseStart_3547176 : Nat := 118140960795 + 3547176 * 2 ^ 59
def prefixEnd_3547176 : Nat := 4983230072969 + 3 ^ 40 * 3547176 * 2
def baseEnd_3547176 : Nat := 1821406254092918891286841

theorem tailTrace_3547176 : CollatzResearch.WordTrace tailWord_3547176 prefixEnd_3547176 1821406254092918891286841 := by
  unfold tailWord_3547176
  simp only [CollatzResearch.WordTrace]
  refine ⟨64688068698597318137478691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86250758264796424183304921 64688068698597318137478691)
  ·
    refine ⟨97032103047895977206218037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64688068698597318137478691 97032103047895977206218037)
    ·
      refine ⟨9096759660740247863082941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97032103047895977206218037 9096759660740247863082941)
      ·
        refine ⟨3411284872777592948656103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9096759660740247863082941 3411284872777592948656103)
        ·
          refine ⟨5116927309166389422984155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3411284872777592948656103 5116927309166389422984155)
          ·
            refine ⟨7675390963749584134476233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5116927309166389422984155 7675390963749584134476233)
            ·
              refine ⟨5756543222812188100857175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7675390963749584134476233 5756543222812188100857175)
              ·
                refine ⟨8634814834218282151285763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5756543222812188100857175 8634814834218282151285763)
                ·
                  refine ⟨12952222251327423226928645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8634814834218282151285763 12952222251327423226928645)
                  ·
                    refine ⟨2428541672123891855049121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12952222251327423226928645 2428541672123891855049121)
                    ·
                      refine ⟨1821406254092918891286841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2428541672123891855049121 1821406254092918891286841)
                      ·
                        rfl

theorem cell23_3547176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_3547176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3547176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3547176 prefixEnd_3547176 := by exact prefixLift 3547176
  have htrace : WordTrace (prefixWord ++ tailWord_3547176) baseStart_3547176 baseEnd_3547176 := by
    simpa [prefixWord, tailWord_3547176, baseEnd_3547176] using wordTrace_append hprefix tailTrace_3547176
  have hstable : (prefixWord ++ tailWord_3547176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547176).length < 2 ^ (prefixWord ++ tailWord_3547176).sum := by decide
  have hdescent : baseEnd_3547176 < baseStart_3547176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547215 : List Nat := [1, 1, 2, 1, 1, 2, 2, 2, 3, 6, 2]
def baseStart_3547215 : Nat := 118140960795 + 3547215 * 2 ^ 59
def prefixEnd_3547215 : Nat := 4983230072969 + 3 ^ 40 * 3547215 * 2
def baseEnd_3547215 : Nat := 1821426279838444238699161

theorem tailTrace_3547215 : CollatzResearch.WordTrace tailWord_3547215 prefixEnd_3547215 1821426279838444238699161 := by
  unfold tailWord_3547215
  simp only [CollatzResearch.WordTrace]
  refine ⟨129377559844053345935627099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86251706562702230623751399 129377559844053345935627099)
  ·
    refine ⟨194066339766080018903440649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129377559844053345935627099 194066339766080018903440649)
    ·
      refine ⟨145549754824560014177580487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194066339766080018903440649 145549754824560014177580487)
      ·
        refine ⟨218324632236840021266370731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145549754824560014177580487 218324632236840021266370731)
        ·
          refine ⟨327486948355260031899556097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218324632236840021266370731 327486948355260031899556097)
          ·
            refine ⟨245615211266445023924667073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 327486948355260031899556097 245615211266445023924667073)
            ·
              refine ⟨184211408449833767943500305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 245615211266445023924667073 184211408449833767943500305)
              ·
                refine ⟨138158556337375325957625229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184211408449833767943500305 138158556337375325957625229)
                ·
                  refine ⟨51809458626515747234109461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138158556337375325957625229 51809458626515747234109461)
                  ·
                    refine ⟨2428568373117925651598881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 51809458626515747234109461 2428568373117925651598881)
                    ·
                      refine ⟨1821426279838444238699161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2428568373117925651598881 1821426279838444238699161)
                      ·
                        rfl

theorem cell23_3547215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 6, 2].length) (baseStart_3547215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3547215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3547215 prefixEnd_3547215 := by exact prefixLift 3547215
  have htrace : WordTrace (prefixWord ++ tailWord_3547215) baseStart_3547215 baseEnd_3547215 := by
    simpa [prefixWord, tailWord_3547215, baseEnd_3547215] using wordTrace_append hprefix tailTrace_3547215
  have hstable : (prefixWord ++ tailWord_3547215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547215).length < 2 ^ (prefixWord ++ tailWord_3547215).sum := by decide
  have hdescent : baseEnd_3547215 < baseStart_3547215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547232 : List Nat := [2, 1, 1, 3, 2, 3, 2, 1, 2, 4, 2]
def baseStart_3547232 : Nat := 118140960795 + 3547232 * 2 ^ 59
def prefixEnd_3547232 : Nat := 4983230072969 + 3 ^ 40 * 3547232 * 2
def baseEnd_3547232 : Nat := 1821435009009570672186583

theorem tailTrace_3547232 : CollatzResearch.WordTrace tailWord_3547232 prefixEnd_3547232 1821435009009570672186583 := by
  unfold tailWord_3547232
  simp only [CollatzResearch.WordTrace]
  refine ⟨64689089942495878919497975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86252119923327838559330633 64689089942495878919497975)
  ·
    refine ⟨97033634913743818379246963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64689089942495878919497975 97033634913743818379246963)
    ·
      refine ⟨145550452370615727568870445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97033634913743818379246963 145550452370615727568870445)
      ·
        refine ⟨54581419638980897838326417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145550452370615727568870445 54581419638980897838326417)
        ·
          refine ⟨40936064729235673378744813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54581419638980897838326417 40936064729235673378744813)
          ·
            refine ⟨15351024273463377517029305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40936064729235673378744813 15351024273463377517029305)
            ·
              refine ⟨11513268205097533137771979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15351024273463377517029305 11513268205097533137771979)
              ·
                refine ⟨17269902307646299706657969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11513268205097533137771979 17269902307646299706657969)
                ·
                  refine ⟨12952426730734724779993477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17269902307646299706657969 12952426730734724779993477)
                  ·
                    refine ⟨2428580012012760896248777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12952426730734724779993477 2428580012012760896248777)
                    ·
                      refine ⟨1821435009009570672186583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2428580012012760896248777 1821435009009570672186583)
                      ·
                        rfl

theorem cell23_3547232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 2, 4, 2].length) (baseStart_3547232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3547232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3547232 prefixEnd_3547232 := by exact prefixLift 3547232
  have htrace : WordTrace (prefixWord ++ tailWord_3547232) baseStart_3547232 baseEnd_3547232 := by
    simpa [prefixWord, tailWord_3547232, baseEnd_3547232] using wordTrace_append hprefix tailTrace_3547232
  have hstable : (prefixWord ++ tailWord_3547232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547232).length < 2 ^ (prefixWord ++ tailWord_3547232).sum := by decide
  have hdescent : baseEnd_3547232 < baseStart_3547232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547235 : List Nat := [1, 1, 1, 5, 1, 1, 3, 2, 1, 4, 3]
def baseStart_3547235 : Nat := 118140960795 + 3547235 * 2 ^ 59
def prefixEnd_3547235 : Nat := 4983230072969 + 3 ^ 40 * 3547235 * 2
def baseEnd_3547235 : Nat := 1821436549451534160449069

theorem tailTrace_3547235 : CollatzResearch.WordTrace tailWord_3547235 prefixEnd_3547235 1821436549451534160449069 := by
  unfold tailWord_3547235
  simp only [CollatzResearch.WordTrace]
  refine ⟨129378289303980889351355159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86252192869320592900903439 129378289303980889351355159)
  ·
    refine ⟨194067433955971334027032739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129378289303980889351355159 194067433955971334027032739)
    ·
      refine ⟨291101150933957001040549109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194067433955971334027032739 291101150933957001040549109)
      ·
        refine ⟨27290732900058468847551479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 291101150933957001040549109 27290732900058468847551479)
        ·
          refine ⟨40936099350087703271327219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27290732900058468847551479 40936099350087703271327219)
          ·
            refine ⟨61404149025131554906990829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40936099350087703271327219 61404149025131554906990829)
            ·
              refine ⟨23026555884424333090121561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61404149025131554906990829 23026555884424333090121561)
              ·
                refine ⟨17269916913318249817591171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23026555884424333090121561 17269916913318249817591171)
                ·
                  refine ⟨25904875369977374726386757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17269916913318249817591171 25904875369977374726386757)
                  ·
                    refine ⟨4857164131870757761197517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25904875369977374726386757 4857164131870757761197517)
                    ·
                      refine ⟨1821436549451534160449069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4857164131870757761197517 1821436549451534160449069)
                      ·
                        rfl

theorem cell23_3547235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_3547235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3547235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3547235 prefixEnd_3547235 := by exact prefixLift 3547235
  have htrace : WordTrace (prefixWord ++ tailWord_3547235) baseStart_3547235 baseEnd_3547235 := by
    simpa [prefixWord, tailWord_3547235, baseEnd_3547235] using wordTrace_append hprefix tailTrace_3547235
  have hstable : (prefixWord ++ tailWord_3547235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547235).length < 2 ^ (prefixWord ++ tailWord_3547235).sum := by decide
  have hdescent : baseEnd_3547235 < baseStart_3547235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547245 : List Nat := [1, 5, 1, 1, 2, 1, 1, 1, 2, 4, 4]
def baseStart_3547245 : Nat := 118140960795 + 3547245 * 2 ^ 59
def prefixEnd_3547245 : Nat := 4983230072969 + 3 ^ 40 * 3547245 * 2
def baseEnd_3547245 : Nat := 1821441684258079121324023

theorem tailTrace_3547245 : CollatzResearch.WordTrace tailWord_3547245 prefixEnd_3547245 1821441684258079121324023 := by
  unfold tailWord_3547245
  simp only [CollatzResearch.WordTrace]
  refine ⟨129378654033944661059219189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86252436022629774039479459 129378654033944661059219189)
  ·
    refine ⟨12129248815682311974301799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 129378654033944661059219189 12129248815682311974301799)
    ·
      refine ⟨18193873223523467961452699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12129248815682311974301799 18193873223523467961452699)
      ·
        refine ⟨27290809835285201942179049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18193873223523467961452699 27290809835285201942179049)
        ·
          refine ⟨20468107376463901456634287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27290809835285201942179049 20468107376463901456634287)
          ·
            refine ⟨30702161064695852184951431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20468107376463901456634287 30702161064695852184951431)
            ·
              refine ⟨46053241597043778277427147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30702161064695852184951431 46053241597043778277427147)
              ·
                refine ⟨69079862395565667416140721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46053241597043778277427147 69079862395565667416140721)
                ·
                  refine ⟨51809896796674250562105541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69079862395565667416140721 51809896796674250562105541)
                  ·
                    refine ⟨9714355649376421980394789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51809896796674250562105541 9714355649376421980394789)
                    ·
                      refine ⟨1821441684258079121324023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9714355649376421980394789 1821441684258079121324023)
                      ·
                        rfl

theorem cell23_3547245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_3547245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3547245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3547245 prefixEnd_3547245 := by exact prefixLift 3547245
  have htrace : WordTrace (prefixWord ++ tailWord_3547245) baseStart_3547245 baseEnd_3547245 := by
    simpa [prefixWord, tailWord_3547245, baseEnd_3547245] using wordTrace_append hprefix tailTrace_3547245
  have hstable : (prefixWord ++ tailWord_3547245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547245).length < 2 ^ (prefixWord ++ tailWord_3547245).sum := by decide
  have hdescent : baseEnd_3547245 < baseStart_3547245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547285 : List Nat := [1, 3, 2, 1, 1, 1, 4, 2, 3, 5]
def baseStart_3547285 : Nat := 118140960795 + 3547285 * 2 ^ 59
def prefixEnd_3547285 : Nat := 4983230072969 + 3 ^ 40 * 3547285 * 2
def baseEnd_3547285 : Nat := 607154074494752988274613

theorem tailTrace_3547285 : CollatzResearch.WordTrace tailWord_3547285 prefixEnd_3547285 607154074494752988274613 := by
  unfold tailWord_3547285
  simp only [CollatzResearch.WordTrace]
  refine ⟨129380112953799747890675309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86253408635866498593783539 129380112953799747890675309)
  ·
    refine ⟨48517542357674905459003241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129380112953799747890675309 48517542357674905459003241)
    ·
      refine ⟨36388156768256179094252431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48517542357674905459003241 36388156768256179094252431)
      ·
        refine ⟨54582235152384268641378647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36388156768256179094252431 54582235152384268641378647)
        ·
          refine ⟨81873352728576402962067971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54582235152384268641378647 81873352728576402962067971)
          ·
            refine ⟨122810029092864604443101957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81873352728576402962067971 122810029092864604443101957)
            ·
              refine ⟨23026880454912113333081617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122810029092864604443101957 23026880454912113333081617)
              ·
                refine ⟨17270160341184084999811213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23026880454912113333081617 17270160341184084999811213)
                ·
                  refine ⟨6476310127944031874929205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17270160341184084999811213 6476310127944031874929205)
                  ·
                    refine ⟨607154074494752988274613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6476310127944031874929205 607154074494752988274613)
                    ·
                      rfl

theorem cell23_3547285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 3, 5].length) (baseStart_3547285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3547285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3547285 prefixEnd_3547285 := by exact prefixLift 3547285
  have htrace : WordTrace (prefixWord ++ tailWord_3547285) baseStart_3547285 baseEnd_3547285 := by
    simpa [prefixWord, tailWord_3547285, baseEnd_3547285] using wordTrace_append hprefix tailTrace_3547285
  have hstable : (prefixWord ++ tailWord_3547285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547285).length < 2 ^ (prefixWord ++ tailWord_3547285).sum := by decide
  have hdescent : baseEnd_3547285 < baseStart_3547285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547319 : List Nat := [1, 1, 3, 1, 4, 3, 3, 1, 1, 5]
def baseStart_3547319 : Nat := 118140960795 + 3547319 * 2 ^ 59
def prefixEnd_3547319 : Nat := 4983230072969 + 3 ^ 40 * 3547319 * 2
def baseEnd_3547319 : Nat := 607159893942170610599561

theorem tailTrace_3547319 : CollatzResearch.WordTrace tailWord_3547319 prefixEnd_3547319 607159893942170610599561 := by
  unfold tailWord_3547319
  simp only [CollatzResearch.WordTrace]
  refine ⟨129381353035676571697413011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86254235357117714464942007 129381353035676571697413011)
  ·
    refine ⟨194072029553514857546119517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129381353035676571697413011 194072029553514857546119517)
    ·
      refine ⟨72777011082568071579794819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194072029553514857546119517 72777011082568071579794819)
      ·
        refine ⟨109165516623852107369692229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72777011082568071579794819 109165516623852107369692229)
        ·
          refine ⟨20468534366972270131817293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109165516623852107369692229 20468534366972270131817293)
          ·
            refine ⟨7675700387614601299431485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20468534366972270131817293 7675700387614601299431485)
            ·
              refine ⟨2878387645355475487286807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7675700387614601299431485 2878387645355475487286807)
              ·
                refine ⟨4317581468033213230930211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2878387645355475487286807 4317581468033213230930211)
                ·
                  refine ⟨6476372202049819846395317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4317581468033213230930211 6476372202049819846395317)
                  ·
                    refine ⟨607159893942170610599561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6476372202049819846395317 607159893942170610599561)
                    ·
                      rfl

theorem cell23_3547319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3, 1, 1, 5].length) (baseStart_3547319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3547319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3547319 prefixEnd_3547319 := by exact prefixLift 3547319
  have htrace : WordTrace (prefixWord ++ tailWord_3547319) baseStart_3547319 baseEnd_3547319 := by
    simpa [prefixWord, tailWord_3547319, baseEnd_3547319] using wordTrace_append hprefix tailTrace_3547319
  have hstable : (prefixWord ++ tailWord_3547319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547319).length < 2 ^ (prefixWord ++ tailWord_3547319).sum := by decide
  have hdescent : baseEnd_3547319 < baseStart_3547319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547322 : List Nat := [3, 1, 1, 1, 2, 2, 2, 5, 1, 1, 4]
def baseStart_3547322 : Nat := 118140960795 + 3547322 * 2 ^ 59
def prefixEnd_3547322 : Nat := 4983230072969 + 3 ^ 40 * 3547322 * 2
def baseEnd_3547322 : Nat := 1821481222268475320061169

theorem tailTrace_3547322 : CollatzResearch.WordTrace tailWord_3547322 prefixEnd_3547322 1821481222268475320061169 := by
  unfold tailWord_3547322
  simp only [CollatzResearch.WordTrace]
  refine ⟨32345365613666425802443055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86254308303110468806514813 32345365613666425802443055)
  ·
    refine ⟨48518048420499638703664583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32345365613666425802443055 48518048420499638703664583)
    ·
      refine ⟨72777072630749458055496875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48518048420499638703664583 72777072630749458055496875)
      ·
        refine ⟨109165608946124187083245313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72777072630749458055496875 109165608946124187083245313)
        ·
          refine ⟨81874206709593140312433985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109165608946124187083245313 81874206709593140312433985)
          ·
            refine ⟨61405655032194855234325489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81874206709593140312433985 61405655032194855234325489)
            ·
              refine ⟨46054241274146141425744117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61405655032194855234325489 46054241274146141425744117)
              ·
                refine ⟨4317585119451200758663511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46054241274146141425744117 4317585119451200758663511)
                ·
                  refine ⟨6476377679176801137995267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4317585119451200758663511 6476377679176801137995267)
                  ·
                    refine ⟨9714566518765201706992901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6476377679176801137995267 9714566518765201706992901)
                    ·
                      refine ⟨1821481222268475320061169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9714566518765201706992901 1821481222268475320061169)
                      ·
                        rfl

theorem cell23_3547322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 5, 1, 1, 4].length) (baseStart_3547322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3547322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3547322 prefixEnd_3547322 := by exact prefixLift 3547322
  have htrace : WordTrace (prefixWord ++ tailWord_3547322) baseStart_3547322 baseEnd_3547322 := by
    simpa [prefixWord, tailWord_3547322, baseEnd_3547322] using wordTrace_append hprefix tailTrace_3547322
  have hstable : (prefixWord ++ tailWord_3547322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547322).length < 2 ^ (prefixWord ++ tailWord_3547322).sum := by decide
  have hdescent : baseEnd_3547322 < baseStart_3547322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547339 : List Nat := [1, 1, 1, 1, 3, 2, 4, 3, 3, 2, 2]
def baseStart_3547339 : Nat := 118140960795 + 3547339 * 2 ^ 59
def prefixEnd_3547339 : Nat := 4983230072969 + 3 ^ 40 * 3547339 * 2
def baseEnd_3547339 : Nat := 1821489951439601753548591

theorem tailTrace_3547339 : CollatzResearch.WordTrace tailWord_3547339 prefixEnd_3547339 1821489951439601753548591 := by
  unfold tailWord_3547339
  simp only [CollatzResearch.WordTrace]
  refine ⟨129382082495604115113141071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86254721663736076742094047 129382082495604115113141071)
  ·
    refine ⟨194073123743406172669711607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129382082495604115113141071 194073123743406172669711607)
    ·
      refine ⟨291109685615109259004567411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194073123743406172669711607 291109685615109259004567411)
      ·
        refine ⟨436664528422663888506851117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291109685615109259004567411 436664528422663888506851117)
        ·
          refine ⟨163749198158498958190069169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 436664528422663888506851117 163749198158498958190069169)
          ·
            refine ⟨122811898618874218642551877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163749198158498958190069169 122811898618874218642551877)
            ·
              refine ⟨23027230991038915995478477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122811898618874218642551877 23027230991038915995478477)
              ·
                refine ⟨8635211621639593498304429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23027230991038915995478477 8635211621639593498304429)
                ·
                  refine ⟨3238204358114847561864161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8635211621639593498304429 3238204358114847561864161)
                  ·
                    refine ⟨2428653268586135671398121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3238204358114847561864161 2428653268586135671398121)
                    ·
                      refine ⟨1821489951439601753548591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2428653268586135671398121 1821489951439601753548591)
                      ·
                        rfl

theorem cell23_3547339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3, 3, 2, 2].length) (baseStart_3547339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3547339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3547339 prefixEnd_3547339 := by exact prefixLift 3547339
  have htrace : WordTrace (prefixWord ++ tailWord_3547339) baseStart_3547339 baseEnd_3547339 := by
    simpa [prefixWord, tailWord_3547339, baseEnd_3547339] using wordTrace_append hprefix tailTrace_3547339
  have hstable : (prefixWord ++ tailWord_3547339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547339).length < 2 ^ (prefixWord ++ tailWord_3547339).sum := by decide
  have hdescent : baseEnd_3547339 < baseStart_3547339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547345 : List Nat := [1, 2, 2, 1, 2, 2, 5, 8]
def baseStart_3547345 : Nat := 118140960795 + 3547345 * 2 ^ 59
def prefixEnd_3547345 : Nat := 4983230072969 + 3 ^ 40 * 3547345 * 2
def baseEnd_3547345 : Nat := 67462704900871434447169

theorem tailTrace_3547345 : CollatzResearch.WordTrace tailWord_3547345 prefixEnd_3547345 67462704900871434447169 := by
  unfold tailWord_3547345
  simp only [CollatzResearch.WordTrace]
  refine ⟨129382301333582378137859489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86254867555721585425239659 129382301333582378137859489)
  ·
    refine ⟨97036726000186783603394617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129382301333582378137859489 97036726000186783603394617)
    ·
      refine ⟨72777544500140087702545963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97036726000186783603394617 72777544500140087702545963)
      ·
        refine ⟨109166316750210131553818945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72777544500140087702545963 109166316750210131553818945)
        ·
          refine ⟨81874737562657598665364209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109166316750210131553818945 81874737562657598665364209)
          ·
            refine ⟨61406053171993198999023157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81874737562657598665364209 61406053171993198999023157)
            ·
              refine ⟨5756817484874362406158421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61406053171993198999023157 5756817484874362406158421)
              ·
                refine ⟨67462704900871434447169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5756817484874362406158421 67462704900871434447169)
                ·
                  rfl

theorem cell23_3547345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 8].length) (baseStart_3547345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3547345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3547345 prefixEnd_3547345 := by exact prefixLift 3547345
  have htrace : WordTrace (prefixWord ++ tailWord_3547345) baseStart_3547345 baseEnd_3547345 := by
    simpa [prefixWord, tailWord_3547345, baseEnd_3547345] using wordTrace_append hprefix tailTrace_3547345
  have hstable : (prefixWord ++ tailWord_3547345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547345).length < 2 ^ (prefixWord ++ tailWord_3547345).sum := by decide
  have hdescent : baseEnd_3547345 < baseStart_3547345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547349 : List Nat := [1, 3, 2, 4, 2, 1, 2, 1, 1, 6]
def baseStart_3547349 : Nat := 118140960795 + 3547349 * 2 ^ 59
def prefixEnd_3547349 : Nat := 4983230072969 + 3 ^ 40 * 3547349 * 2
def baseEnd_3547349 : Nat := 607165028748715571474515

theorem tailTrace_3547349 : CollatzResearch.WordTrace tailWord_3547349 prefixEnd_3547349 607165028748715571474515 := by
  unfold tailWord_3547349
  simp only [CollatzResearch.WordTrace]
  refine ⟨129382447225567886821005101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86254964817045257880670067 129382447225567886821005101)
  ·
    refine ⟨48518417709587957557876913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129382447225567886821005101 48518417709587957557876913)
    ·
      refine ⟨36388813282190968168407685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48518417709587957557876913 36388813282190968168407685)
      ·
        refine ⟨6822902490410806531576441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36388813282190968168407685 6822902490410806531576441)
        ·
          refine ⟨5117176867808104898682331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6822902490410806531576441 5117176867808104898682331)
          ·
            refine ⟨7675765301712157348023497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5117176867808104898682331 7675765301712157348023497)
            ·
              refine ⟨5756823976284118011017623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7675765301712157348023497 5756823976284118011017623)
              ·
                refine ⟨8635235964426177016526435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5756823976284118011017623 8635235964426177016526435)
                ·
                  refine ⟨12952853946639265524789653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8635235964426177016526435 12952853946639265524789653)
                  ·
                    refine ⟨607165028748715571474515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12952853946639265524789653 607165028748715571474515)
                    ·
                      rfl

theorem cell23_3547349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 1, 1, 6].length) (baseStart_3547349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3547349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3547349 prefixEnd_3547349 := by exact prefixLift 3547349
  have htrace : WordTrace (prefixWord ++ tailWord_3547349) baseStart_3547349 baseEnd_3547349 := by
    simpa [prefixWord, tailWord_3547349, baseEnd_3547349] using wordTrace_append hprefix tailTrace_3547349
  have hstable : (prefixWord ++ tailWord_3547349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547349).length < 2 ^ (prefixWord ++ tailWord_3547349).sum := by decide
  have hdescent : baseEnd_3547349 < baseStart_3547349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547352 : List Nat := [2, 1, 2, 2, 4, 1, 1, 3, 1, 2, 4]
def baseStart_3547352 : Nat := 118140960795 + 3547352 * 2 ^ 59
def prefixEnd_3547352 : Nat := 4983230072969 + 3 ^ 40 * 3547352 * 2
def baseEnd_3547352 : Nat := 1821496626688110202686031

theorem tailTrace_3547352 : CollatzResearch.WordTrace tailWord_3547352 prefixEnd_3547352 1821496626688110202686031 := by
  unfold tailWord_3547352
  simp only [CollatzResearch.WordTrace]
  refine ⟨64691278322278509166682155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86255037763038012222242873 64691278322278509166682155)
  ·
    refine ⟨97036917483417763750023233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64691278322278509166682155 97036917483417763750023233)
    ·
      refine ⟨72777688112563322812517425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97036917483417763750023233 72777688112563322812517425)
      ·
        refine ⟨54583266084422492109388069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72777688112563322812517425 54583266084422492109388069)
        ·
          refine ⟨10234362390829217270510263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54583266084422492109388069 10234362390829217270510263)
          ·
            refine ⟨15351543586243825905765395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10234362390829217270510263 15351543586243825905765395)
            ·
              refine ⟨23027315379365738858648093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15351543586243825905765395 23027315379365738858648093)
              ·
                refine ⟨8635243267262152071993035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23027315379365738858648093 8635243267262152071993035)
                ·
                  refine ⟨12952864900893228107989553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8635243267262152071993035 12952864900893228107989553)
                  ·
                    refine ⟨9714648675669921080992165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12952864900893228107989553 9714648675669921080992165)
                    ·
                      refine ⟨1821496626688110202686031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9714648675669921080992165 1821496626688110202686031)
                      ·
                        rfl

theorem cell23_3547352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 3, 1, 2, 4].length) (baseStart_3547352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3547352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3547352 prefixEnd_3547352 := by exact prefixLift 3547352
  have htrace : WordTrace (prefixWord ++ tailWord_3547352) baseStart_3547352 baseEnd_3547352 := by
    simpa [prefixWord, tailWord_3547352, baseEnd_3547352] using wordTrace_append hprefix tailTrace_3547352
  have hstable : (prefixWord ++ tailWord_3547352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547352).length < 2 ^ (prefixWord ++ tailWord_3547352).sum := by decide
  have hdescent : baseEnd_3547352 < baseStart_3547352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547372 : List Nat := [2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 3]
def baseStart_3547372 : Nat := 118140960795 + 3547372 * 2 ^ 59
def prefixEnd_3547372 : Nat := 4983230072969 + 3 ^ 40 * 3547372 * 2
def baseEnd_3547372 : Nat := 1821506896301200124435939

theorem tailTrace_3547372 : CollatzResearch.WordTrace tailWord_3547372 prefixEnd_3547372 1821506896301200124435939 := by
  unfold tailWord_3547372
  simp only [CollatzResearch.WordTrace]
  refine ⟨64691643052242280874546185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86255524069656374499394913 64691643052242280874546185)
  ·
    refine ⟨48518732289181710655909639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64691643052242280874546185 48518732289181710655909639)
    ·
      refine ⟨72778098433772565983864459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48518732289181710655909639 72778098433772565983864459)
      ·
        refine ⟨109167147650658848975796689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72778098433772565983864459 109167147650658848975796689)
        ·
          refine ⟨81875360737994136731847517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109167147650658848975796689 81875360737994136731847517)
          ·
            refine ⟨30703260276747801274442819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81875360737994136731847517 30703260276747801274442819)
            ·
              refine ⟨46054890415121701911664229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30703260276747801274442819 46054890415121701911664229)
              ·
                refine ⟨8635291952835319108437043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46054890415121701911664229 8635291952835319108437043)
                ·
                  refine ⟨12952937929252978662655565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8635291952835319108437043 12952937929252978662655565)
                  ·
                    refine ⟨4857351723469866998495837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12952937929252978662655565 4857351723469866998495837)
                    ·
                      refine ⟨1821506896301200124435939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4857351723469866998495837 1821506896301200124435939)
                      ·
                        rfl

theorem cell23_3547372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 3].length) (baseStart_3547372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3547372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3547372 prefixEnd_3547372 := by exact prefixLift 3547372
  have htrace : WordTrace (prefixWord ++ tailWord_3547372) baseStart_3547372 baseEnd_3547372 := by
    simpa [prefixWord, tailWord_3547372, baseEnd_3547372] using wordTrace_append hprefix tailTrace_3547372
  have hstable : (prefixWord ++ tailWord_3547372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547372).length < 2 ^ (prefixWord ++ tailWord_3547372).sum := by decide
  have hdescent : baseEnd_3547372 < baseStart_3547372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547373 : List Nat := [1, 5, 1, 2, 3, 2, 2, 1, 1, 1, 4]
def baseStart_3547373 : Nat := 118140960795 + 3547373 * 2 ^ 59
def prefixEnd_3547373 : Nat := 4983230072969 + 3 ^ 40 * 3547373 * 2
def baseEnd_3547373 : Nat := 1821507409781854620523435

theorem tailTrace_3547373 : CollatzResearch.WordTrace tailWord_3547373 prefixEnd_3547373 1821507409781854620523435 := by
  unfold tailWord_3547373
  simp only [CollatzResearch.WordTrace]
  refine ⟨129383322577480938919878773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86255548384987292613252515 129383322577480938919878773)
  ·
    refine ⟨12129686491638838023738635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 129383322577480938919878773 12129686491638838023738635)
    ·
      refine ⟨18194529737458257035607953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12129686491638838023738635 18194529737458257035607953)
      ·
        refine ⟨13645897303093692776705965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18194529737458257035607953 13645897303093692776705965)
        ·
          refine ⟨5117211488660134791264737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13645897303093692776705965 5117211488660134791264737)
          ·
            refine ⟨3837908616495101093448553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5117211488660134791264737 3837908616495101093448553)
            ·
              refine ⟨2878431462371325820086415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3837908616495101093448553 2878431462371325820086415)
              ·
                refine ⟨4317647193556988730129623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2878431462371325820086415 4317647193556988730129623)
                ·
                  refine ⟨6476470790335483095194435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4317647193556988730129623 6476470790335483095194435)
                  ·
                    refine ⟨9714706185503224642791653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6476470790335483095194435 9714706185503224642791653)
                    ·
                      refine ⟨1821507409781854620523435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9714706185503224642791653 1821507409781854620523435)
                      ·
                        rfl

theorem cell23_3547373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_3547373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3547373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3547373 prefixEnd_3547373 := by exact prefixLift 3547373
  have htrace : WordTrace (prefixWord ++ tailWord_3547373) baseStart_3547373 baseEnd_3547373 := by
    simpa [prefixWord, tailWord_3547373, baseEnd_3547373] using wordTrace_append hprefix tailTrace_3547373
  have hstable : (prefixWord ++ tailWord_3547373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547373).length < 2 ^ (prefixWord ++ tailWord_3547373).sum := by decide
  have hdescent : baseEnd_3547373 < baseStart_3547373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547385 : List Nat := [1, 2, 1, 3, 1, 1, 2, 1, 4, 2, 5]
def baseStart_3547385 : Nat := 118140960795 + 3547385 * 2 ^ 59
def prefixEnd_3547385 : Nat := 4983230072969 + 3 ^ 40 * 3547385 * 2
def baseEnd_3547385 : Nat := 1821513571549708573573379

theorem tailTrace_3547385 : CollatzResearch.WordTrace tailWord_3547385 prefixEnd_3547385 1821513571549708573573379 := by
  unfold tailWord_3547385
  simp only [CollatzResearch.WordTrace]
  refine ⟨129383760253437464969315609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86255840168958309979543739 129383760253437464969315609)
  ·
    refine ⟨97037820190078098726986707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129383760253437464969315609 97037820190078098726986707)
    ·
      refine ⟨145556730285117148090480061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97037820190078098726986707 145556730285117148090480061)
      ·
        refine ⟨54583773856918930533930023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145556730285117148090480061 54583773856918930533930023)
        ·
          refine ⟨81875660785378395800895035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54583773856918930533930023 81875660785378395800895035)
          ·
            refine ⟨122813491178067593701342553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81875660785378395800895035 122813491178067593701342553)
            ·
              refine ⟨92110118383550695276006915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122813491178067593701342553 92110118383550695276006915)
              ·
                refine ⟨138165177575326042914010373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92110118383550695276006915 138165177575326042914010373)
                ·
                  refine ⟨25905970795373633046376945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 138165177575326042914010373 25905970795373633046376945)
                  ·
                    refine ⟨19429478096530224784782709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25905970795373633046376945 19429478096530224784782709)
                    ·
                      refine ⟨1821513571549708573573379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19429478096530224784782709 1821513571549708573573379)
                      ·
                        rfl

theorem cell23_3547385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_3547385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3547385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3547385 prefixEnd_3547385 := by exact prefixLift 3547385
  have htrace : WordTrace (prefixWord ++ tailWord_3547385) baseStart_3547385 baseEnd_3547385 := by
    simpa [prefixWord, tailWord_3547385, baseEnd_3547385] using wordTrace_append hprefix tailTrace_3547385
  have hstable : (prefixWord ++ tailWord_3547385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547385).length < 2 ^ (prefixWord ++ tailWord_3547385).sum := by decide
  have hdescent : baseEnd_3547385 < baseStart_3547385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547416 : List Nat := [2, 1, 2, 3, 1, 2, 4, 2, 1, 3, 2]
def baseStart_3547416 : Nat := 118140960795 + 3547416 * 2 ^ 59
def prefixEnd_3547416 : Nat := 4983230072969 + 3 ^ 40 * 3547416 * 2
def baseEnd_3547416 : Nat := 1821529489449997952285737

theorem tailTrace_3547416 : CollatzResearch.WordTrace tailWord_3547416 prefixEnd_3547416 1821529489449997952285737 := by
  unfold tailWord_3547416
  simp only [CollatzResearch.WordTrace]
  refine ⟨64692445458162578631847051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86256593944216771509129401 64692445458162578631847051)
  ·
    refine ⟨97038668187243867947770577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64692445458162578631847051 97038668187243867947770577)
    ·
      refine ⟨72779001140432900960827933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97038668187243867947770577 72779001140432900960827933)
      ·
        refine ⟨27292125427662337860310475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72779001140432900960827933 27292125427662337860310475)
        ·
          refine ⟨40938188141493506790465713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27292125427662337860310475 40938188141493506790465713)
          ·
            refine ⟨30703641106120130092849285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40938188141493506790465713 30703641106120130092849285)
            ·
              refine ⟨5756932707397524392409241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30703641106120130092849285 5756932707397524392409241)
              ·
                refine ⟨4317699530548143294306931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5756932707397524392409241 4317699530548143294306931)
                ·
                  refine ⟨6476549295822214941460397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4317699530548143294306931 6476549295822214941460397)
                  ·
                    refine ⟨2428705985933330603047649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6476549295822214941460397 2428705985933330603047649)
                    ·
                      refine ⟨1821529489449997952285737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2428705985933330603047649 1821529489449997952285737)
                      ·
                        rfl

theorem cell23_3547416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 2, 1, 3, 2].length) (baseStart_3547416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3547416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3547416 prefixEnd_3547416 := by exact prefixLift 3547416
  have htrace : WordTrace (prefixWord ++ tailWord_3547416) baseStart_3547416 baseEnd_3547416 := by
    simpa [prefixWord, tailWord_3547416, baseEnd_3547416] using wordTrace_append hprefix tailTrace_3547416
  have hstable : (prefixWord ++ tailWord_3547416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547416).length < 2 ^ (prefixWord ++ tailWord_3547416).sum := by decide
  have hdescent : baseEnd_3547416 < baseStart_3547416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547457 : List Nat := [1, 2, 5, 2, 3, 1, 2, 1, 2, 1, 3]
def baseStart_3547457 : Nat := 118140960795 + 3547457 * 2 ^ 59
def prefixEnd_3547457 : Nat := 4983230072969 + 3 ^ 40 * 3547457 * 2
def baseEnd_3547457 : Nat := 1821550542156832291873049

theorem tailTrace_3547457 : CollatzResearch.WordTrace tailWord_3547457 prefixEnd_3547457 1821550542156832291873049 := by
  unfold tailWord_3547457
  simp only [CollatzResearch.WordTrace]
  refine ⟨129386386309176621265936625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86257590872784414177291083 129386386309176621265936625)
  ·
    refine ⟨97039789731882465949452469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129386386309176621265936625 97039789731882465949452469)
    ·
      refine ⟨9097480287363981182761169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97039789731882465949452469 9097480287363981182761169)
      ·
        refine ⟨6823110215522985887070877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9097480287363981182761169 6823110215522985887070877)
        ·
          refine ⟨2558666330821119707651579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6823110215522985887070877 2558666330821119707651579)
          ·
            refine ⟨3837999496231679561477369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2558666330821119707651579 3837999496231679561477369)
            ·
              refine ⟨2878499622173759671108027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3837999496231679561477369 2878499622173759671108027)
              ·
                refine ⟨4317749433260639506662041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2878499622173759671108027 4317749433260639506662041)
                ·
                  refine ⟨3238312074945479629996531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4317749433260639506662041 3238312074945479629996531)
                  ·
                    refine ⟨4857468112418219444994797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3238312074945479629996531 4857468112418219444994797)
                    ·
                      refine ⟨1821550542156832291873049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4857468112418219444994797 1821550542156832291873049)
                      ·
                        rfl

theorem cell23_3547457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_3547457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3547457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3547457 prefixEnd_3547457 := by exact prefixLift 3547457
  have htrace : WordTrace (prefixWord ++ tailWord_3547457) baseStart_3547457 baseEnd_3547457 := by
    simpa [prefixWord, tailWord_3547457, baseEnd_3547457] using wordTrace_append hprefix tailTrace_3547457
  have hstable : (prefixWord ++ tailWord_3547457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547457).length < 2 ^ (prefixWord ++ tailWord_3547457).sum := by decide
  have hdescent : baseEnd_3547457 < baseStart_3547457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547492 : List Nat := [2, 3, 1, 1, 3, 1, 1, 1, 3, 2, 5]
def baseStart_3547492 : Nat := 118140960795 + 3547492 * 2 ^ 59
def prefixEnd_3547492 : Nat := 4983230072969 + 3 ^ 40 * 3547492 * 2
def baseEnd_3547492 : Nat := 1821568513979739654935387

theorem tailTrace_3547492 : CollatzResearch.WordTrace tailWord_3547492 prefixEnd_3547492 1821568513979739654935387 := by
  unfold tailWord_3547492
  simp only [CollatzResearch.WordTrace]
  refine ⟨64693831432024911121730365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86258441909366548162307153 64693831432024911121730365)
  ·
    refine ⟨24260186787009341670648887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64693831432024911121730365 24260186787009341670648887)
    ·
      refine ⟨36390280180514012505973331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24260186787009341670648887 36390280180514012505973331)
      ·
        refine ⟨54585420270771018758959997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36390280180514012505973331 54585420270771018758959997)
        ·
          refine ⟨20469532601539132034609999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54585420270771018758959997 20469532601539132034609999)
          ·
            refine ⟨30704298902308698051914999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20469532601539132034609999 30704298902308698051914999)
            ·
              refine ⟨46056448353463047077872499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30704298902308698051914999 46056448353463047077872499)
              ·
                refine ⟨69084672530194570616808749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46056448353463047077872499 69084672530194570616808749)
                ·
                  refine ⟨25906752198822963981303281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69084672530194570616808749 25906752198822963981303281)
                  ·
                    refine ⟨19430064149117222985977461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25906752198822963981303281 19430064149117222985977461)
                    ·
                      refine ⟨1821568513979739654935387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19430064149117222985977461 1821568513979739654935387)
                      ·
                        rfl

theorem cell23_3547492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_3547492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3547492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3547492 prefixEnd_3547492 := by exact prefixLift 3547492
  have htrace : WordTrace (prefixWord ++ tailWord_3547492) baseStart_3547492 baseEnd_3547492 := by
    simpa [prefixWord, tailWord_3547492, baseEnd_3547492] using wordTrace_append hprefix tailTrace_3547492
  have hstable : (prefixWord ++ tailWord_3547492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547492).length < 2 ^ (prefixWord ++ tailWord_3547492).sum := by decide
  have hdescent : baseEnd_3547492 < baseStart_3547492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547509 : List Nat := [1, 3, 4, 1, 2, 1, 2, 1, 1, 2, 5]
def baseStart_3547509 : Nat := 118140960795 + 3547509 * 2 ^ 59
def prefixEnd_3547509 : Nat := 4983230072969 + 3 ^ 40 * 3547509 * 2
def baseEnd_3547509 : Nat := 1821577243150866088422809

theorem tailTrace_3547509 : CollatzResearch.WordTrace tailWord_3547509 prefixEnd_3547509 1821577243150866088422809 := by
  unfold tailWord_3547509
  simp only [CollatzResearch.WordTrace]
  refine ⟨129388282904988234146829581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86258855269992156097886387 129388282904988234146829581)
  ·
    refine ⟨48520606089370587805061093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129388282904988234146829581 48520606089370587805061093)
    ·
      refine ⟨9097613641756985213448955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48520606089370587805061093 9097613641756985213448955)
      ·
        refine ⟨13646420462635477820173433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9097613641756985213448955 13646420462635477820173433)
        ·
          refine ⟨10234815346976608365130075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13646420462635477820173433 10234815346976608365130075)
          ·
            refine ⟨15352223020464912547695113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10234815346976608365130075 15352223020464912547695113)
            ·
              refine ⟨11514167265348684410771335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15352223020464912547695113 11514167265348684410771335)
              ·
                refine ⟨17271250898023026616157003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11514167265348684410771335 17271250898023026616157003)
                ·
                  refine ⟨25906876347034539924235505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17271250898023026616157003 25906876347034539924235505)
                  ·
                    refine ⟨19430157260275904943176629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25906876347034539924235505 19430157260275904943176629)
                    ·
                      refine ⟨1821577243150866088422809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19430157260275904943176629 1821577243150866088422809)
                      ·
                        rfl

theorem cell23_3547509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_3547509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3547509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3547509 prefixEnd_3547509 := by exact prefixLift 3547509
  have htrace : WordTrace (prefixWord ++ tailWord_3547509) baseStart_3547509 baseEnd_3547509 := by
    simpa [prefixWord, tailWord_3547509, baseEnd_3547509] using wordTrace_append hprefix tailTrace_3547509
  have hstable : (prefixWord ++ tailWord_3547509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547509).length < 2 ^ (prefixWord ++ tailWord_3547509).sum := by decide
  have hdescent : baseEnd_3547509 < baseStart_3547509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547519 : List Nat := [1, 1, 2, 2, 1, 1, 2, 5, 2, 4, 2]
def baseStart_3547519 : Nat := 118140960795 + 3547519 * 2 ^ 59
def prefixEnd_3547519 : Nat := 4983230072969 + 3 ^ 40 * 3547519 * 2
def baseEnd_3547519 : Nat := 1821582377957411049297763

theorem tailTrace_3547519 : CollatzResearch.WordTrace tailWord_3547519 prefixEnd_3547519 1821582377957411049297763 := by
  unfold tailWord_3547519
  simp only [CollatzResearch.WordTrace]
  refine ⟨129388647634952005854693611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86259098423301337236462407 129388647634952005854693611)
  ·
    refine ⟨194082971452428008782040417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129388647634952005854693611 194082971452428008782040417)
    ·
      refine ⟨145562228589321006586530313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194082971452428008782040417 145562228589321006586530313)
      ·
        refine ⟨109171671441990754939897735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145562228589321006586530313 109171671441990754939897735)
        ·
          refine ⟨163757507162986132409846603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109171671441990754939897735 163757507162986132409846603)
          ·
            refine ⟨245636260744479198614769905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163757507162986132409846603 245636260744479198614769905)
            ·
              refine ⟨184227195558359398961077429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 245636260744479198614769905 184227195558359398961077429)
              ·
                refine ⟨17271299583596193652601009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 184227195558359398961077429 17271299583596193652601009)
                ·
                  refine ⟨12953474687697145239450757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17271299583596193652601009 12953474687697145239450757)
                  ·
                    refine ⟨2428776503943214732397017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12953474687697145239450757 2428776503943214732397017)
                    ·
                      refine ⟨1821582377957411049297763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2428776503943214732397017 1821582377957411049297763)
                      ·
                        rfl

theorem cell23_3547519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 2, 4, 2].length) (baseStart_3547519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3547519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3547519 prefixEnd_3547519 := by exact prefixLift 3547519
  have htrace : WordTrace (prefixWord ++ tailWord_3547519) baseStart_3547519 baseEnd_3547519 := by
    simpa [prefixWord, tailWord_3547519, baseEnd_3547519] using wordTrace_append hprefix tailTrace_3547519
  have hstable : (prefixWord ++ tailWord_3547519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547519).length < 2 ^ (prefixWord ++ tailWord_3547519).sum := by decide
  have hdescent : baseEnd_3547519 < baseStart_3547519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547529 : List Nat := [1, 2, 1, 1, 6, 1, 1, 1, 5, 4]
def baseStart_3547529 : Nat := 118140960795 + 3547529 * 2 ^ 59
def prefixEnd_3547529 : Nat := 4983230072969 + 3 ^ 40 * 3547529 * 2
def baseEnd_3547529 : Nat := 607195837587985336724239

theorem tailTrace_3547529 : CollatzResearch.WordTrace tailWord_3547529 prefixEnd_3547529 607195837587985336724239 := by
  unfold tailWord_3547529
  simp only [CollatzResearch.WordTrace]
  refine ⟨129389012364915777562557641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86259341576610518375038427 129389012364915777562557641)
  ·
    refine ⟨97041759273686833171918231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129389012364915777562557641 97041759273686833171918231)
    ·
      refine ⟨145562638910530249757877347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97041759273686833171918231 145562638910530249757877347)
      ·
        refine ⟨218343958365795374636816021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145562638910530249757877347 218343958365795374636816021)
        ·
          refine ⟨10234873048396658186100751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 218343958365795374636816021 10234873048396658186100751)
          ·
            refine ⟨15352309572594987279151127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10234873048396658186100751 15352309572594987279151127)
            ·
              refine ⟨23028464358892480918726691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15352309572594987279151127 23028464358892480918726691)
              ·
                refine ⟨34542696538338721378090037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23028464358892480918726691 34542696538338721378090037)
                ·
                  refine ⟨3238377800469255129195941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34542696538338721378090037 3238377800469255129195941)
                  ·
                    refine ⟨607195837587985336724239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3238377800469255129195941 607195837587985336724239)
                    ·
                      rfl

theorem cell23_3547529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 5, 4].length) (baseStart_3547529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3547529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3547529 prefixEnd_3547529 := by exact prefixLift 3547529
  have htrace : WordTrace (prefixWord ++ tailWord_3547529) baseStart_3547529 baseEnd_3547529 := by
    simpa [prefixWord, tailWord_3547529, baseEnd_3547529] using wordTrace_append hprefix tailTrace_3547529
  have hstable : (prefixWord ++ tailWord_3547529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547529).length < 2 ^ (prefixWord ++ tailWord_3547529).sum := by decide
  have hdescent : baseEnd_3547529 < baseStart_3547529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547559 : List Nat := [1, 1, 6, 1, 1, 3, 1, 1, 8]
def baseStart_3547559 : Nat := 118140960795 + 3547559 * 2 ^ 59
def prefixEnd_3547559 : Nat := 4983230072969 + 3 ^ 40 * 3547559 * 2
def baseEnd_3547559 : Nat := 202400324131510099199731

theorem tailTrace_3547559 : CollatzResearch.WordTrace tailWord_3547559 prefixEnd_3547559 202400324131510099199731 := by
  unfold tailWord_3547559
  simp only [CollatzResearch.WordTrace]
  refine ⟨129390106554807092686149731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86260071036538061790766487 129390106554807092686149731)
  ·
    refine ⟨194085159832210639029224597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129390106554807092686149731 194085159832210639029224597)
    ·
      refine ⟨9097741867134873704494903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 194085159832210639029224597 9097741867134873704494903)
      ·
        refine ⟨13646612800702310556742355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9097741867134873704494903 13646612800702310556742355)
        ·
          refine ⟨20469919201053465835113533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13646612800702310556742355 20469919201053465835113533)
          ·
            refine ⟨7676219700395049688167575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20469919201053465835113533 7676219700395049688167575)
            ·
              refine ⟨11514329550592574532251363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7676219700395049688167575 11514329550592574532251363)
              ·
                refine ⟨17271494325888861798377045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11514329550592574532251363 17271494325888861798377045)
                ·
                  refine ⟨202400324131510099199731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17271494325888861798377045 202400324131510099199731)
                  ·
                    rfl

theorem cell23_3547559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 8].length) (baseStart_3547559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3547559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3547559 prefixEnd_3547559 := by exact prefixLift 3547559
  have htrace : WordTrace (prefixWord ++ tailWord_3547559) baseStart_3547559 baseEnd_3547559 := by
    simpa [prefixWord, tailWord_3547559, baseEnd_3547559] using wordTrace_append hprefix tailTrace_3547559
  have hstable : (prefixWord ++ tailWord_3547559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547559).length < 2 ^ (prefixWord ++ tailWord_3547559).sum := by decide
  have hdescent : baseEnd_3547559 < baseStart_3547559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547613 : List Nat := [1, 4, 3, 1, 1, 1, 3, 2, 2, 3, 2]
def baseStart_3547613 : Nat := 118140960795 + 3547613 * 2 ^ 59
def prefixEnd_3547613 : Nat := 4983230072969 + 3 ^ 40 * 3547613 * 2
def baseEnd_3547613 : Nat := 1821630645138933681522331

theorem tailTrace_3547613 : CollatzResearch.WordTrace tailWord_3547613 prefixEnd_3547613 1821630645138933681522331 := by
  unfold tailWord_3547613
  simp only [CollatzResearch.WordTrace]
  refine ⟨129392076096611459908615493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86261384064407639939076995 129392076096611459908615493)
  ·
    refine ⟨24261014268114648732865405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129392076096611459908615493 24261014268114648732865405)
    ·
      refine ⟨9097880350542993274824527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24261014268114648732865405 9097880350542993274824527)
      ·
        refine ⟨13646820525814489912236791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9097880350542993274824527 13646820525814489912236791)
        ·
          refine ⟨20470230788721734868355187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13646820525814489912236791 20470230788721734868355187)
          ·
            refine ⟨30705346183082602302532781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20470230788721734868355187 30705346183082602302532781)
            ·
              refine ⟨11514504818655975863449793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30705346183082602302532781 11514504818655975863449793)
              ·
                refine ⟨8635878613991981897587345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11514504818655975863449793 8635878613991981897587345)
                ·
                  refine ⟨6476908960493986423190509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8635878613991981897587345 6476908960493986423190509)
                  ·
                    refine ⟨2428840860185244908696441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6476908960493986423190509 2428840860185244908696441)
                    ·
                      refine ⟨1821630645138933681522331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2428840860185244908696441 1821630645138933681522331)
                      ·
                        rfl

theorem cell23_3547613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_3547613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3547613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3547613 prefixEnd_3547613 := by exact prefixLift 3547613
  have htrace : WordTrace (prefixWord ++ tailWord_3547613) baseStart_3547613 baseEnd_3547613 := by
    simpa [prefixWord, tailWord_3547613, baseEnd_3547613] using wordTrace_append hprefix tailTrace_3547613
  have hstable : (prefixWord ++ tailWord_3547613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547613).length < 2 ^ (prefixWord ++ tailWord_3547613).sum := by decide
  have hdescent : baseEnd_3547613 < baseStart_3547613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547649 : List Nat := [1, 2, 4, 1, 3, 1, 2, 9]
def baseStart_3547649 : Nat := 118140960795 + 3547649 * 2 ^ 59
def prefixEnd_3547649 : Nat := 4983230072969 + 3 ^ 40 * 3547649 * 2
def baseEnd_3547649 : Nat := 67468486312685020024895

theorem tailTrace_3547649 : CollatzResearch.WordTrace tailWord_3547649 prefixEnd_3547649 67468486312685020024895 := by
  unfold tailWord_3547649
  simp only [CollatzResearch.WordTrace]
  refine ⟨129393389124481038056926001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86262259416320692037950667 129393389124481038056926001)
  ·
    refine ⟨97045041843360778542694501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129393389124481038056926001 97045041843360778542694501)
    ·
      refine ⟨18195945345630145976755219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97045041843360778542694501 18195945345630145976755219)
      ·
        refine ⟨27293918018445218965132829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18195945345630145976755219 27293918018445218965132829)
        ·
          refine ⟨10235219256916957111924811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27293918018445218965132829 10235219256916957111924811)
          ·
            refine ⟨15352828885375435667887217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10235219256916957111924811 15352828885375435667887217)
            ·
              refine ⟨11514621664031576750915413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15352828885375435667887217 11514621664031576750915413)
              ·
                refine ⟨67468486312685020024895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11514621664031576750915413 67468486312685020024895)
                ·
                  rfl

theorem cell23_3547649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 9].length) (baseStart_3547649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3547649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3547649 prefixEnd_3547649 := by exact prefixLift 3547649
  have htrace : WordTrace (prefixWord ++ tailWord_3547649) baseStart_3547649 baseEnd_3547649 := by
    simpa [prefixWord, tailWord_3547649, baseEnd_3547649] using wordTrace_append hprefix tailTrace_3547649
  have hstable : (prefixWord ++ tailWord_3547649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547649).length < 2 ^ (prefixWord ++ tailWord_3547649).sum := by decide
  have hdescent : baseEnd_3547649 < baseStart_3547649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547671 : List Nat := [1, 1, 3, 6, 2, 1, 2, 2, 1, 1, 3]
def baseStart_3547671 : Nat := 118140960795 + 3547671 * 2 ^ 59
def prefixEnd_3547671 : Nat := 4983230072969 + 3 ^ 40 * 3547671 * 2
def baseEnd_3547671 : Nat := 1821660427016894454597065

theorem tailTrace_3547671 : CollatzResearch.WordTrace tailWord_3547671 prefixEnd_3547671 1821660427016894454597065 := by
  unfold tailWord_3547671
  simp only [CollatzResearch.WordTrace]
  refine ⟨129394191530401335814226867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86262794353600890542817911 129394191530401335814226867)
  ·
    refine ⟨194091287295602003721340301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129394191530401335814226867 194091287295602003721340301)
    ·
      refine ⟨72784232735850751395502613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194091287295602003721340301 72784232735850751395502613)
      ·
        refine ⟨3411760909493003971664185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 72784232735850751395502613 3411760909493003971664185)
        ·
          refine ⟨2558820682119752978748139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3411760909493003971664185 2558820682119752978748139)
          ·
            refine ⟨3838231023179629468122209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2558820682119752978748139 3838231023179629468122209)
            ·
              refine ⟨2878673267384722101091657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3838231023179629468122209 2878673267384722101091657)
              ·
                refine ⟨2159004950538541575818743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2878673267384722101091657 2159004950538541575818743)
                ·
                  refine ⟨3238507425807812363728115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2159004950538541575818743 3238507425807812363728115)
                  ·
                    refine ⟨4857761138711718545592173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3238507425807812363728115 4857761138711718545592173)
                    ·
                      refine ⟨1821660427016894454597065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4857761138711718545592173 1821660427016894454597065)
                      ·
                        rfl

theorem cell23_3547671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_3547671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3547671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3547671 prefixEnd_3547671 := by exact prefixLift 3547671
  have htrace : WordTrace (prefixWord ++ tailWord_3547671) baseStart_3547671 baseEnd_3547671 := by
    simpa [prefixWord, tailWord_3547671, baseEnd_3547671] using wordTrace_append hprefix tailTrace_3547671
  have hstable : (prefixWord ++ tailWord_3547671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547671).length < 2 ^ (prefixWord ++ tailWord_3547671).sum := by decide
  have hdescent : baseEnd_3547671 < baseStart_3547671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547677 : List Nat := [1, 4, 2, 2, 1, 3, 1, 4, 1, 2, 2]
def baseStart_3547677 : Nat := 118140960795 + 3547677 * 2 ^ 59
def prefixEnd_3547677 : Nat := 4983230072969 + 3 ^ 40 * 3547677 * 2
def baseEnd_3547677 : Nat := 1821663507900821431122037

theorem tailTrace_3547677 : CollatzResearch.WordTrace tailWord_3547677 prefixEnd_3547677 1821663507900821431122037 := by
  unfold tailWord_3547677
  simp only [CollatzResearch.WordTrace]
  refine ⟨129394410368379598838945285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86262940245586399225963523 129394410368379598838945285)
  ·
    refine ⟨24261451944071174782302241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129394410368379598838945285 24261451944071174782302241)
    ·
      refine ⟨18196088958053381086726681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24261451944071174782302241 18196088958053381086726681)
      ·
        refine ⟨13647066718540035815045011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18196088958053381086726681 13647066718540035815045011)
        ·
          refine ⟨20470600077810053722567517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13647066718540035815045011 20470600077810053722567517)
          ·
            refine ⟨7676475029178770145962819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20470600077810053722567517 7676475029178770145962819)
            ·
              refine ⟨11514712543768155218944229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7676475029178770145962819 11514712543768155218944229)
              ·
                refine ⟨2159008601956529103552043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11514712543768155218944229 2159008601956529103552043)
                ·
                  refine ⟨3238512902934793655328065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2159008601956529103552043 3238512902934793655328065)
                  ·
                    refine ⟨2428884677201095241496049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3238512902934793655328065 2428884677201095241496049)
                    ·
                      refine ⟨1821663507900821431122037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2428884677201095241496049 1821663507900821431122037)
                      ·
                        rfl

theorem cell23_3547677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_3547677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3547677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3547677 prefixEnd_3547677 := by exact prefixLift 3547677
  have htrace : WordTrace (prefixWord ++ tailWord_3547677) baseStart_3547677 baseEnd_3547677 := by
    simpa [prefixWord, tailWord_3547677, baseEnd_3547677] using wordTrace_append hprefix tailTrace_3547677
  have hstable : (prefixWord ++ tailWord_3547677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547677).length < 2 ^ (prefixWord ++ tailWord_3547677).sum := by decide
  have hdescent : baseEnd_3547677 < baseStart_3547677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547699 : List Nat := [1, 1, 1, 2, 4, 2, 1, 2, 2, 3, 4]
def baseStart_3547699 : Nat := 118140960795 + 3547699 * 2 ^ 59
def prefixEnd_3547699 : Nat := 4983230072969 + 3 ^ 40 * 3547699 * 2
def baseEnd_3547699 : Nat := 1821674804475220345046935

theorem tailTrace_3547699 : CollatzResearch.WordTrace tailWord_3547699 prefixEnd_3547699 1821674804475220345046935 := by
  unfold tailWord_3547699
  simp only [CollatzResearch.WordTrace]
  refine ⟨129395212774299896596246151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86263475182866597730830767 129395212774299896596246151)
  ·
    refine ⟨194092819161449844894369227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129395212774299896596246151 194092819161449844894369227)
    ·
      refine ⟨291139228742174767341553841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194092819161449844894369227 291139228742174767341553841)
      ·
        refine ⟨218354421556631075506165381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291139228742174767341553841 218354421556631075506165381)
        ·
          refine ⟨40941454041868326657406009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 218354421556631075506165381 40941454041868326657406009)
          ·
            refine ⟨30706090531401244993054507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40941454041868326657406009 30706090531401244993054507)
            ·
              refine ⟨46059135797101867489581761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30706090531401244993054507 46059135797101867489581761)
              ·
                refine ⟨34544351847826400617186321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46059135797101867489581761 34544351847826400617186321)
                ·
                  refine ⟨25908263885869800462889741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34544351847826400617186321 25908263885869800462889741)
                  ·
                    refine ⟨9715598957201175173583653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25908263885869800462889741 9715598957201175173583653)
                    ·
                      refine ⟨1821674804475220345046935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9715598957201175173583653 1821674804475220345046935)
                      ·
                        rfl

theorem cell23_3547699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 3, 4].length) (baseStart_3547699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3547699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3547699 prefixEnd_3547699 := by exact prefixLift 3547699
  have htrace : WordTrace (prefixWord ++ tailWord_3547699) baseStart_3547699 baseEnd_3547699 := by
    simpa [prefixWord, tailWord_3547699, baseEnd_3547699] using wordTrace_append hprefix tailTrace_3547699
  have hstable : (prefixWord ++ tailWord_3547699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547699).length < 2 ^ (prefixWord ++ tailWord_3547699).sum := by decide
  have hdescent : baseEnd_3547699 < baseStart_3547699 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547700 : List Nat := [2, 5, 1, 3, 1, 1, 3, 7]
def baseStart_3547700 : Nat := 118140960795 + 3547700 * 2 ^ 59
def prefixEnd_3547700 : Nat := 4983230072969 + 3 ^ 40 * 3547700 * 2
def baseEnd_3547700 : Nat := 67469456220587957079053

theorem tailTrace_3547700 : CollatzResearch.WordTrace tailWord_3547700 prefixEnd_3547700 67469456220587957079053 := by
  unfold tailWord_3547700
  simp only [CollatzResearch.WordTrace]
  refine ⟨64697624623648136883516277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86263499498197515844688369 64697624623648136883516277)
  ·
    refine ⟨6065402308467012832829651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64697624623648136883516277 6065402308467012832829651)
    ·
      refine ⟨9098103462700519249244477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6065402308467012832829651 9098103462700519249244477)
      ·
        refine ⟨3411788798512694718466679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9098103462700519249244477 3411788798512694718466679)
        ·
          refine ⟨5117683197769042077700019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3411788798512694718466679 5117683197769042077700019)
          ·
            refine ⟨7676524796653563116550029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5117683197769042077700019 7676524796653563116550029)
            ·
              refine ⟨2878696798745086168706261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7676524796653563116550029 2878696798745086168706261)
              ·
                refine ⟨67469456220587957079053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2878696798745086168706261 67469456220587957079053)
                ·
                  rfl

theorem cell23_3547700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3, 7].length) (baseStart_3547700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3547700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3547700 prefixEnd_3547700 := by exact prefixLift 3547700
  have htrace : WordTrace (prefixWord ++ tailWord_3547700) baseStart_3547700 baseEnd_3547700 := by
    simpa [prefixWord, tailWord_3547700, baseEnd_3547700] using wordTrace_append hprefix tailTrace_3547700
  have hstable : (prefixWord ++ tailWord_3547700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547700).length < 2 ^ (prefixWord ++ tailWord_3547700).sum := by decide
  have hdescent : baseEnd_3547700 < baseStart_3547700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547703 : List Nat := [1, 1, 3, 1, 2, 3, 2, 4, 1, 3, 2]
def baseStart_3547703 : Nat := 118140960795 + 3547703 * 2 ^ 59
def prefixEnd_3547703 : Nat := 4983230072969 + 3 ^ 40 * 3547703 * 2
def baseEnd_3547703 : Nat := 1821676858397838329396917

theorem tailTrace_3547703 : CollatzResearch.WordTrace tailWord_3547703 prefixEnd_3547703 1821676858397838329396917 := by
  unfold tailWord_3547703
  simp only [CollatzResearch.WordTrace]
  refine ⟨129395358666285405279391763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86263572444190270186261175 129395358666285405279391763)
  ·
    refine ⟨194093037999428107919087645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129395358666285405279391763 194093037999428107919087645)
    ·
      refine ⟨72784889249785540469657867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194093037999428107919087645 72784889249785540469657867)
      ·
        refine ⟨109177333874678310704486801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72784889249785540469657867 109177333874678310704486801)
        ·
          refine ⟨81883000406008733028365101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109177333874678310704486801 81883000406008733028365101)
          ·
            refine ⟨30706125152253274885636913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81883000406008733028365101 30706125152253274885636913)
            ·
              refine ⟨23029593864189956164227685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30706125152253274885636913 23029593864189956164227685)
              ·
                refine ⟨4318048849535616780792691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23029593864189956164227685 4318048849535616780792691)
                ·
                  refine ⟨6477073274303425171189037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4318048849535616780792691 6477073274303425171189037)
                  ·
                    refine ⟨2428902477863784439195889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6477073274303425171189037 2428902477863784439195889)
                    ·
                      refine ⟨1821676858397838329396917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2428902477863784439195889 1821676858397838329396917)
                      ·
                        rfl

theorem cell23_3547703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 4, 1, 3, 2].length) (baseStart_3547703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3547703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3547703 prefixEnd_3547703 := by exact prefixLift 3547703
  have htrace : WordTrace (prefixWord ++ tailWord_3547703) baseStart_3547703 baseEnd_3547703 := by
    simpa [prefixWord, tailWord_3547703, baseEnd_3547703] using wordTrace_append hprefix tailTrace_3547703
  have hstable : (prefixWord ++ tailWord_3547703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547703).length < 2 ^ (prefixWord ++ tailWord_3547703).sum := by decide
  have hdescent : baseEnd_3547703 < baseStart_3547703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547790 : List Nat := [4, 1, 1, 3, 1, 1, 5, 2, 5]
def baseStart_3547790 : Nat := 118140960795 + 3547790 * 2 ^ 59
def prefixEnd_3547790 : Nat := 4983230072969 + 3 ^ 40 * 3547790 * 2
def baseEnd_3547790 : Nat := 202413503468308832112113

theorem tailTrace_3547790 : CollatzResearch.WordTrace tailWord_3547790 prefixEnd_3547790 202413503468308832112113 := by
  unfold tailWord_3547790
  simp only [CollatzResearch.WordTrace]
  refine ⟨16174816477121277392226103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86265687877980146091872549 16174816477121277392226103)
  ·
    refine ⟨24262224715681916088339155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16174816477121277392226103 24262224715681916088339155)
    ·
      refine ⟨36393337073522874132508733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24262224715681916088339155 36393337073522874132508733)
      ·
        refine ⟨13647501402571077799690775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36393337073522874132508733 13647501402571077799690775)
        ·
          refine ⟨20471252103856616699536163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13647501402571077799690775 20471252103856616699536163)
          ·
            refine ⟨30706878155784925049304245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20471252103856616699536163 30706878155784925049304245)
            ·
              refine ⟨2878769827104836723372273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30706878155784925049304245 2878769827104836723372273)
              ·
                refine ⟨2159077370328627542529205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2878769827104836723372273 2159077370328627542529205)
                ·
                  refine ⟨202413503468308832112113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2159077370328627542529205 202413503468308832112113)
                  ·
                    rfl

theorem cell23_3547790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5, 2, 5].length) (baseStart_3547790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3547790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3547790 prefixEnd_3547790 := by exact prefixLift 3547790
  have htrace : WordTrace (prefixWord ++ tailWord_3547790) baseStart_3547790 baseEnd_3547790 := by
    simpa [prefixWord, tailWord_3547790, baseEnd_3547790] using wordTrace_append hprefix tailTrace_3547790
  have hstable : (prefixWord ++ tailWord_3547790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547790).length < 2 ^ (prefixWord ++ tailWord_3547790).sum := by decide
  have hdescent : baseEnd_3547790 < baseStart_3547790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547823 : List Nat := [1, 1, 2, 1, 2, 6, 2, 1, 2, 1, 4]
def baseStart_3547823 : Nat := 118140960795 + 3547823 * 2 ^ 59
def prefixEnd_3547823 : Nat := 4983230072969 + 3 ^ 40 * 3547823 * 2
def baseEnd_3547823 : Nat := 1821738476076377859896365

theorem tailTrace_3547823 : CollatzResearch.WordTrace tailWord_3547823 prefixEnd_3547823 1821738476076377859896365 := by
  unfold tailWord_3547823
  simp only [CollatzResearch.WordTrace]
  refine ⟨129399735425850665773760123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86266490283900443849173415 129399735425850665773760123)
  ·
    refine ⟨194099603138775998660640185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129399735425850665773760123 194099603138775998660640185)
    ·
      refine ⟨145574702354081998995480139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194099603138775998660640185 145574702354081998995480139)
      ·
        refine ⟨218362053531122998493220209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145574702354081998995480139 218362053531122998493220209)
        ·
          refine ⟨163771540148342248869915157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218362053531122998493220209 163771540148342248869915157)
          ·
            refine ⟨7676790944453542915777273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 163771540148342248869915157 7676790944453542915777273)
            ·
              refine ⟨5757593208340157186832955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7676790944453542915777273 5757593208340157186832955)
              ·
                refine ⟨8636389812510235780249433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5757593208340157186832955 8636389812510235780249433)
                ·
                  refine ⟨6477292359382676835187075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8636389812510235780249433 6477292359382676835187075)
                  ·
                    refine ⟨9715938539074015252780613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6477292359382676835187075 9715938539074015252780613)
                    ·
                      refine ⟨1821738476076377859896365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9715938539074015252780613 1821738476076377859896365)
                      ·
                        rfl

theorem cell23_3547823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 1, 2, 1, 4].length) (baseStart_3547823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3547823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3547823 prefixEnd_3547823 := by exact prefixLift 3547823
  have htrace : WordTrace (prefixWord ++ tailWord_3547823) baseStart_3547823 baseEnd_3547823 := by
    simpa [prefixWord, tailWord_3547823, baseEnd_3547823] using wordTrace_append hprefix tailTrace_3547823
  have hstable : (prefixWord ++ tailWord_3547823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547823).length < 2 ^ (prefixWord ++ tailWord_3547823).sum := by decide
  have hdescent : baseEnd_3547823 < baseStart_3547823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547836 : List Nat := [2, 2, 2, 3, 1, 1, 2, 1, 2, 1, 6]
def baseStart_3547836 : Nat := 118140960795 + 3547836 * 2 ^ 59
def prefixEnd_3547836 : Nat := 4983230072969 + 3 ^ 40 * 3547836 * 2
def baseEnd_3547836 : Nat := 1821745151324886309033805

theorem tailTrace_3547836 : CollatzResearch.WordTrace tailWord_3547836 prefixEnd_3547836 1821745151324886309033805 := by
  unfold tailWord_3547836
  simp only [CollatzResearch.WordTrace]
  refine ⟨64700104787401784496991681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86266806383202379329322241 64700104787401784496991681)
  ·
    refine ⟨48525078590551338372743761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64700104787401784496991681 48525078590551338372743761)
    ·
      refine ⟨36393808942913503779557821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48525078590551338372743761 36393808942913503779557821)
      ·
        refine ⟨13647678353592563917334183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36393808942913503779557821 13647678353592563917334183)
        ·
          refine ⟨20471517530388845876001275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13647678353592563917334183 20471517530388845876001275)
          ·
            refine ⟨30707276295583268814001913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20471517530388845876001275 30707276295583268814001913)
            ·
              refine ⟨23030457221687451610501435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30707276295583268814001913 23030457221687451610501435)
              ·
                refine ⟨34545685832531177415752153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23030457221687451610501435 34545685832531177415752153)
                ·
                  refine ⟨25909264374398383061814115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34545685832531177415752153 25909264374398383061814115)
                  ·
                    refine ⟨38863896561597574592721173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25909264374398383061814115 38863896561597574592721173)
                    ·
                      refine ⟨1821745151324886309033805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38863896561597574592721173 1821745151324886309033805)
                      ·
                        rfl

theorem cell23_3547836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_3547836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3547836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3547836 prefixEnd_3547836 := by exact prefixLift 3547836
  have htrace : WordTrace (prefixWord ++ tailWord_3547836) baseStart_3547836 baseEnd_3547836 := by
    simpa [prefixWord, tailWord_3547836, baseEnd_3547836] using wordTrace_append hprefix tailTrace_3547836
  have hstable : (prefixWord ++ tailWord_3547836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547836).length < 2 ^ (prefixWord ++ tailWord_3547836).sum := by decide
  have hdescent : baseEnd_3547836 < baseStart_3547836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547841 : List Nat := [1, 2, 6, 2, 2, 1, 2, 2, 5]
def baseStart_3547841 : Nat := 118140960795 + 3547841 * 2 ^ 59
def prefixEnd_3547841 : Nat := 4983230072969 + 3 ^ 40 * 3547841 * 2
def baseEnd_3547841 : Nat := 202416413192017643274587

theorem tailTrace_3547841 : CollatzResearch.WordTrace tailWord_3547841 prefixEnd_3547841 202416413192017643274587 := by
  unfold tailWord_3547841
  simp only [CollatzResearch.WordTrace]
  refine ⟨129400391939785454847915377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86266927959856969898610251 129400391939785454847915377)
  ·
    refine ⟨97050293954839091135936533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129400391939785454847915377 97050293954839091135936533)
    ·
      refine ⟨4549232529133082396997025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 97050293954839091135936533 4549232529133082396997025)
      ·
        refine ⟨3411924396849811797747769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4549232529133082396997025 3411924396849811797747769)
        ·
          refine ⟨2558943297637358848310827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3411924396849811797747769 2558943297637358848310827)
          ·
            refine ⟨3838414946456038272466241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2558943297637358848310827 3838414946456038272466241)
            ·
              refine ⟨2878811209842028704349681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3838414946456038272466241 2878811209842028704349681)
              ·
                refine ⟨2159108407381521528262261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2878811209842028704349681 2159108407381521528262261)
                ·
                  refine ⟨202416413192017643274587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2159108407381521528262261 202416413192017643274587)
                  ·
                    rfl

theorem cell23_3547841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 2, 2, 5].length) (baseStart_3547841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3547841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3547841 prefixEnd_3547841 := by exact prefixLift 3547841
  have htrace : WordTrace (prefixWord ++ tailWord_3547841) baseStart_3547841 baseEnd_3547841 := by
    simpa [prefixWord, tailWord_3547841, baseEnd_3547841] using wordTrace_append hprefix tailTrace_3547841
  have hstable : (prefixWord ++ tailWord_3547841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547841).length < 2 ^ (prefixWord ++ tailWord_3547841).sum := by decide
  have hdescent : baseEnd_3547841 < baseStart_3547841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547930 : List Nat := [3, 1, 1, 3, 2, 1, 4, 2, 1, 1, 4]
def baseStart_3547930 : Nat := 118140960795 + 3547930 * 2 ^ 59
def prefixEnd_3547930 : Nat := 4983230072969 + 3 ^ 40 * 3547930 * 2
def baseEnd_3547930 : Nat := 1821793418506408941258373

theorem tailTrace_3547930 : CollatzResearch.WordTrace tailWord_3547930 prefixEnd_3547930 1821793418506408941258373 := by
  unfold tailWord_3547930
  simp only [CollatzResearch.WordTrace]
  refine ⟨32350909509115755761976311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86269092024308682031936829 32350909509115755761976311)
  ·
    refine ⟨48526364263673633642964467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32350909509115755761976311 48526364263673633642964467)
    ·
      refine ⟨72789546395510450464446701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48526364263673633642964467 72789546395510450464446701)
      ·
        refine ⟨27296079898316418924167513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72789546395510450464446701 27296079898316418924167513)
        ·
          refine ⟨20472059923737314193125635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27296079898316418924167513 20472059923737314193125635)
          ·
            refine ⟨30708089885605971289688453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20472059923737314193125635 30708089885605971289688453)
            ·
              refine ⟨5757766853551119616816585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30708089885605971289688453 5757766853551119616816585)
              ·
                refine ⟨4318325140163339712612439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5757766853551119616816585 4318325140163339712612439)
                ·
                  refine ⟨6477487710245009568918659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4318325140163339712612439 6477487710245009568918659)
                  ·
                    refine ⟨9716231565367514353377989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6477487710245009568918659 9716231565367514353377989)
                    ·
                      refine ⟨1821793418506408941258373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9716231565367514353377989 1821793418506408941258373)
                      ·
                        rfl

theorem cell23_3547930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 2, 1, 1, 4].length) (baseStart_3547930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3547930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3547930 prefixEnd_3547930 := by exact prefixLift 3547930
  have htrace : WordTrace (prefixWord ++ tailWord_3547930) baseStart_3547930 baseEnd_3547930 := by
    simpa [prefixWord, tailWord_3547930, baseEnd_3547930] using wordTrace_append hprefix tailTrace_3547930
  have hstable : (prefixWord ++ tailWord_3547930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547930).length < 2 ^ (prefixWord ++ tailWord_3547930).sum := by decide
  have hdescent : baseEnd_3547930 < baseStart_3547930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547950 : List Nat := [4, 1, 3, 2, 1, 1, 1, 3, 1, 1, 5]
def baseStart_3547950 : Nat := 118140960795 + 3547950 * 2 ^ 59
def prefixEnd_3547950 : Nat := 4983230072969 + 3 ^ 40 * 3547950 * 2
def baseEnd_3547950 : Nat := 1821803688119498863008281

theorem tailTrace_3547950 : CollatzResearch.WordTrace tailWord_3547950 prefixEnd_3547950 1821803688119498863008281 := by
  unfold tailWord_3547950
  simp only [CollatzResearch.WordTrace]
  refine ⟨16175545937048820807954163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86269578330927044309088869 16175545937048820807954163)
  ·
    refine ⟨24263318905573231211931245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16175545937048820807954163 24263318905573231211931245)
    ·
      refine ⟨9098744589589961704474217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24263318905573231211931245 9098744589589961704474217)
      ·
        refine ⟨6824058442192471278355663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9098744589589961704474217 6824058442192471278355663)
        ·
          refine ⟨10236087663288706917533495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6824058442192471278355663 10236087663288706917533495)
          ·
            refine ⟨15354131494933060376300243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10236087663288706917533495 15354131494933060376300243)
            ·
              refine ⟨23031197242399590564450365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15354131494933060376300243 23031197242399590564450365)
              ·
                refine ⟨8636698965899846461668887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23031197242399590564450365 8636698965899846461668887)
                ·
                  refine ⟨12955048448849769692503331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8636698965899846461668887 12955048448849769692503331)
                  ·
                    refine ⟨19432572673274654538754997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12955048448849769692503331 19432572673274654538754997)
                    ·
                      refine ⟨1821803688119498863008281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19432572673274654538754997 1821803688119498863008281)
                      ·
                        rfl

theorem cell23_3547950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_3547950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3547950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3547950 prefixEnd_3547950 := by exact prefixLift 3547950
  have htrace : WordTrace (prefixWord ++ tailWord_3547950) baseStart_3547950 baseEnd_3547950 := by
    simpa [prefixWord, tailWord_3547950, baseEnd_3547950] using wordTrace_append hprefix tailTrace_3547950
  have hstable : (prefixWord ++ tailWord_3547950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547950).length < 2 ^ (prefixWord ++ tailWord_3547950).sum := by decide
  have hdescent : baseEnd_3547950 < baseStart_3547950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547958 : List Nat := [5, 1, 2, 2, 2, 1, 3, 2, 1, 1, 3]
def baseStart_3547958 : Nat := 118140960795 + 3547958 * 2 ^ 59
def prefixEnd_3547958 : Nat := 4983230072969 + 3 ^ 40 * 3547958 * 2
def baseEnd_3547958 : Nat := 1821807795964734831708245

theorem tailTrace_3547958 : CollatzResearch.WordTrace tailWord_3547958 prefixEnd_3547958 1821807795964734831708245 := by
  unfold tailWord_3547958
  simp only [CollatzResearch.WordTrace]
  refine ⟨8087791205022598989370283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86269772853574389219949685 8087791205022598989370283)
  ·
    refine ⟨12131686807533898484055425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8087791205022598989370283 12131686807533898484055425)
    ·
      refine ⟨9098765105650423863041569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12131686807533898484055425 9098765105650423863041569)
      ·
        refine ⟨6824073829237817897281177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9098765105650423863041569 6824073829237817897281177)
        ·
          refine ⟨5118055371928363422960883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6824073829237817897281177 5118055371928363422960883)
          ·
            refine ⟨7677083057892545134441325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5118055371928363422960883 7677083057892545134441325)
            ·
              refine ⟨2878906146709704425415497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7677083057892545134441325 2878906146709704425415497)
              ·
                refine ⟨2159179610032278319061623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2878906146709704425415497 2159179610032278319061623)
                ·
                  refine ⟨3238769415048417478592435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2159179610032278319061623 3238769415048417478592435)
                  ·
                    refine ⟨4858154122572626217888653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3238769415048417478592435 4858154122572626217888653)
                    ·
                      refine ⟨1821807795964734831708245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4858154122572626217888653 1821807795964734831708245)
                      ·
                        rfl

theorem cell23_3547958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_3547958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3547958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3547958 prefixEnd_3547958 := by exact prefixLift 3547958
  have htrace : WordTrace (prefixWord ++ tailWord_3547958) baseStart_3547958 baseEnd_3547958 := by
    simpa [prefixWord, tailWord_3547958, baseEnd_3547958] using wordTrace_append hprefix tailTrace_3547958
  have hstable : (prefixWord ++ tailWord_3547958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547958).length < 2 ^ (prefixWord ++ tailWord_3547958).sum := by decide
  have hdescent : baseEnd_3547958 < baseStart_3547958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3547981 : List Nat := [1, 6, 1, 2, 3, 1, 1, 2, 1, 1, 4]
def baseStart_3547981 : Nat := 118140960795 + 3547981 * 2 ^ 59
def prefixEnd_3547981 : Nat := 4983230072969 + 3 ^ 40 * 3547981 * 2
def baseEnd_3547981 : Nat := 1821819606019788241720639

theorem tailTrace_3547981 : CollatzResearch.WordTrace tailWord_3547981 prefixEnd_3547981 1821819606019788241720639 := by
  unfold tailWord_3547981
  simp only [CollatzResearch.WordTrace]
  refine ⟨129405498159278258758011797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86270332106185505838674531 129405498159278258758011797)
  ·
    refine ⟨6065882726216168379281803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 129405498159278258758011797 6065882726216168379281803)
    ·
      refine ⟨9098824089324252568922705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6065882726216168379281803 9098824089324252568922705)
      ·
        refine ⟨6824118066993189426692029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9098824089324252568922705 6824118066993189426692029)
        ·
          refine ⟨2559044275122446035009511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6824118066993189426692029 2559044275122446035009511)
          ·
            refine ⟨3838566412683669052514267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2559044275122446035009511 3838566412683669052514267)
            ·
              refine ⟨5757849619025503578771401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3838566412683669052514267 5757849619025503578771401)
              ·
                refine ⟨4318387214269127684078551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5757849619025503578771401 4318387214269127684078551)
                ·
                  refine ⟨6477580821403691526117827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4318387214269127684078551 6477580821403691526117827)
                  ·
                    refine ⟨9716371232105537289176741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6477580821403691526117827 9716371232105537289176741)
                    ·
                      refine ⟨1821819606019788241720639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9716371232105537289176741 1821819606019788241720639)
                      ·
                        rfl

theorem cell23_3547981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_3547981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3547981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3547981 prefixEnd_3547981 := by exact prefixLift 3547981
  have htrace : WordTrace (prefixWord ++ tailWord_3547981) baseStart_3547981 baseEnd_3547981 := by
    simpa [prefixWord, tailWord_3547981, baseEnd_3547981] using wordTrace_append hprefix tailTrace_3547981
  have hstable : (prefixWord ++ tailWord_3547981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3547981).length < 2 ^ (prefixWord ++ tailWord_3547981).sum := by decide
  have hdescent : baseEnd_3547981 < baseStart_3547981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3547981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548013 : List Nat := [1, 5, 1, 1, 1, 1, 1, 4, 2, 6]
def baseStart_3548013 : Nat := 118140960795 + 3548013 * 2 ^ 59
def prefixEnd_3548013 : Nat := 4983230072969 + 3 ^ 40 * 3548013 * 2
def baseEnd_3548013 : Nat := 607278679133577372173497

theorem tailTrace_3548013 : CollatzResearch.WordTrace tailWord_3548013 prefixEnd_3548013 607278679133577372173497 := by
  unfold tailWord_3548013
  simp only [CollatzResearch.WordTrace]
  refine ⟨129406665295162328223176693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86271110196774885482117795 129406665295162328223176693)
  ·
    refine ⟨12131874871421468270922815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 129406665295162328223176693 12131874871421468270922815)
    ·
      refine ⟨18197812307132202406384223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12131874871421468270922815 18197812307132202406384223)
      ·
        refine ⟨27296718460698303609576335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18197812307132202406384223 27296718460698303609576335)
        ·
          refine ⟨40945077691047455414364503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27296718460698303609576335 40945077691047455414364503)
          ·
            refine ⟨61417616536571183121546755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40945077691047455414364503 61417616536571183121546755)
            ·
              refine ⟨92126424804856774682320133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61417616536571183121546755 92126424804856774682320133)
              ·
                refine ⟨17273704650910645252935025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92126424804856774682320133 17273704650910645252935025)
                ·
                  refine ⟨12955278488182983939701269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17273704650910645252935025 12955278488182983939701269)
                  ·
                    refine ⟨607278679133577372173497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12955278488182983939701269 607278679133577372173497)
                    ·
                      rfl

theorem cell23_3548013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_3548013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3548013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3548013 prefixEnd_3548013 := by exact prefixLift 3548013
  have htrace : WordTrace (prefixWord ++ tailWord_3548013) baseStart_3548013 baseEnd_3548013 := by
    simpa [prefixWord, tailWord_3548013, baseEnd_3548013] using wordTrace_append hprefix tailTrace_3548013
  have hstable : (prefixWord ++ tailWord_3548013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548013).length < 2 ^ (prefixWord ++ tailWord_3548013).sum := by decide
  have hdescent : baseEnd_3548013 < baseStart_3548013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548037 : List Nat := [1, 3, 1, 1, 3, 4, 2, 1, 1, 4, 2]
def baseStart_3548037 : Nat := 118140960795 + 3548037 * 2 ^ 59
def prefixEnd_3548037 : Nat := 4983230072969 + 3 ^ 40 * 3548037 * 2
def baseEnd_3548037 : Nat := 1821848360936440022620381

theorem tailTrace_3548037 : CollatzResearch.WordTrace tailWord_3548037 prefixEnd_3548037 1821848360936440022620381 := by
  unfold tailWord_3548037
  simp only [CollatzResearch.WordTrace]
  refine ⟨129407540647075380322050365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86271693764716920214700243 129407540647075380322050365)
  ·
    refine ⟨48527827742653267620768887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129407540647075380322050365 48527827742653267620768887)
    ·
      refine ⟨72791741613979901431153331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48527827742653267620768887 72791741613979901431153331)
      ·
        refine ⟨109187612420969852146729997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72791741613979901431153331 109187612420969852146729997)
        ·
          refine ⟨40945354657863694555023749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109187612420969852146729997 40945354657863694555023749)
          ·
            refine ⟨7677253998349442729066953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40945354657863694555023749 7677253998349442729066953)
            ·
              refine ⟨5757940498762082046800215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7677253998349442729066953 5757940498762082046800215)
              ·
                refine ⟨8636910748143123070200323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5757940498762082046800215 8636910748143123070200323)
                ·
                  refine ⟨12955366122214684605300485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8636910748143123070200323 12955366122214684605300485)
                  ·
                    refine ⟨2429131147915253363493841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12955366122214684605300485 2429131147915253363493841)
                    ·
                      refine ⟨1821848360936440022620381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2429131147915253363493841 1821848360936440022620381)
                      ·
                        rfl

theorem cell23_3548037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 1, 1, 4, 2].length) (baseStart_3548037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3548037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3548037 prefixEnd_3548037 := by exact prefixLift 3548037
  have htrace : WordTrace (prefixWord ++ tailWord_3548037) baseStart_3548037 baseEnd_3548037 := by
    simpa [prefixWord, tailWord_3548037, baseEnd_3548037] using wordTrace_append hprefix tailTrace_3548037
  have hstable : (prefixWord ++ tailWord_3548037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548037).length < 2 ^ (prefixWord ++ tailWord_3548037).sum := by decide
  have hdescent : baseEnd_3548037 < baseStart_3548037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548058 : List Nat := [3, 1, 1, 4, 4, 1, 2, 1, 1, 3, 2]
def baseStart_3548058 : Nat := 118140960795 + 3548058 * 2 ^ 59
def prefixEnd_3548058 : Nat := 4983230072969 + 3 ^ 40 * 3548058 * 2
def baseEnd_3548058 : Nat := 1821859144030184440457785

theorem tailTrace_3548058 : CollatzResearch.WordTrace tailWord_3548058 prefixEnd_3548058 1821859144030184440457785 := by
  unfold tailWord_3548058
  simp only [CollatzResearch.WordTrace]
  refine ⟨32352076644999825227141207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86272204386666200605709885 32352076644999825227141207)
  ·
    refine ⟨48528114967499737840711811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32352076644999825227141207 48528114967499737840711811)
    ·
      refine ⟨72792172451249606761067717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48528114967499737840711811 72792172451249606761067717)
      ·
        refine ⟨13648532334609301267700197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72792172451249606761067717 13648532334609301267700197)
        ·
          refine ⟨2559099812739243987693787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13648532334609301267700197 2559099812739243987693787)
          ·
            refine ⟨3838649719108865981540681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2559099812739243987693787 3838649719108865981540681)
            ·
              refine ⟨2878987289331649486155511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3838649719108865981540681 2878987289331649486155511)
              ·
                refine ⟨4318480933997474229233267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2878987289331649486155511 4318480933997474229233267)
                ·
                  refine ⟨6477721400996211343849901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4318480933997474229233267 6477721400996211343849901)
                  ·
                    refine ⟨2429145525373579253943713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6477721400996211343849901 2429145525373579253943713)
                    ·
                      refine ⟨1821859144030184440457785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2429145525373579253943713 1821859144030184440457785)
                      ·
                        rfl

theorem cell23_3548058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_3548058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3548058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3548058 prefixEnd_3548058 := by exact prefixLift 3548058
  have htrace : WordTrace (prefixWord ++ tailWord_3548058) baseStart_3548058 baseEnd_3548058 := by
    simpa [prefixWord, tailWord_3548058, baseEnd_3548058] using wordTrace_append hprefix tailTrace_3548058
  have hstable : (prefixWord ++ tailWord_3548058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548058).length < 2 ^ (prefixWord ++ tailWord_3548058).sum := by decide
  have hdescent : baseEnd_3548058 < baseStart_3548058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548073 : List Nat := [1, 2, 1, 1, 1, 1, 6, 1, 4, 5]
def baseStart_3548073 : Nat := 118140960795 + 3548073 * 2 ^ 59
def prefixEnd_3548073 : Nat := 4983230072969 + 3 ^ 40 * 3548073 * 2
def baseEnd_3548073 : Nat := 607288948746667293923405

theorem tailTrace_3548073 : CollatzResearch.WordTrace tailWord_3548073 prefixEnd_3548073 607288948746667293923405 := by
  unfold tailWord_3548073
  simp only [CollatzResearch.WordTrace]
  refine ⟨129408853674944958470360873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86272569116629972313573915 129408853674944958470360873)
  ·
    refine ⟨97056640256208718852770655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129408853674944958470360873 97056640256208718852770655)
    ·
      refine ⟨145584960384313078279155983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97056640256208718852770655 145584960384313078279155983)
      ·
        refine ⟨218377440576469617418733975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145584960384313078279155983 218377440576469617418733975)
        ·
          refine ⟨327566160864704426128100963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218377440576469617418733975 327566160864704426128100963)
          ·
            refine ⟨491349241297056639192151445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327566160864704426128100963 491349241297056639192151445)
            ·
              refine ⟨23031995685799529962132099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 491349241297056639192151445 23031995685799529962132099)
              ·
                refine ⟨34547993528699294943198149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23031995685799529962132099 34547993528699294943198149)
                ·
                  refine ⟨6477748786631117801849653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34547993528699294943198149 6477748786631117801849653)
                  ·
                    refine ⟨607288948746667293923405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6477748786631117801849653 607288948746667293923405)
                    ·
                      rfl

theorem cell23_3548073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 4, 5].length) (baseStart_3548073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3548073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3548073 prefixEnd_3548073 := by exact prefixLift 3548073
  have htrace : WordTrace (prefixWord ++ tailWord_3548073) baseStart_3548073 baseEnd_3548073 := by
    simpa [prefixWord, tailWord_3548073, baseEnd_3548073] using wordTrace_append hprefix tailTrace_3548073
  have hstable : (prefixWord ++ tailWord_3548073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548073).length < 2 ^ (prefixWord ++ tailWord_3548073).sum := by decide
  have hdescent : baseEnd_3548073 < baseStart_3548073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548110 : List Nat := [4, 1, 1, 1, 2, 3, 2, 1, 1, 3, 4]
def baseStart_3548110 : Nat := 118140960795 + 3548110 * 2 ^ 59
def prefixEnd_3548110 : Nat := 4983230072969 + 3 ^ 40 * 3548110 * 2
def baseEnd_3548110 : Nat := 1821885845024218237007545

theorem tailTrace_3548110 : CollatzResearch.WordTrace tailWord_3548110 prefixEnd_3548110 1821885845024218237007545 := by
  unfold tailWord_3548110
  simp only [CollatzResearch.WordTrace]
  refine ⟨16176275396976364223682223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86273468783873942526305189 16176275396976364223682223)
  ·
    refine ⟨24264413095464546335523335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16176275396976364223682223 24264413095464546335523335)
    ·
      refine ⟨36396619643196819503285003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24264413095464546335523335 36396619643196819503285003)
      ·
        refine ⟨54594929464795229254927505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36396619643196819503285003 54594929464795229254927505)
        ·
          refine ⟨40946197098596421941195629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54594929464795229254927505 40946197098596421941195629)
          ·
            refine ⟨15354823911973658227948361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40946197098596421941195629 15354823911973658227948361)
            ·
              refine ⟨11516117933980243670961271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15354823911973658227948361 11516117933980243670961271)
              ·
                refine ⟨17274176900970365506441907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11516117933980243670961271 17274176900970365506441907)
                ·
                  refine ⟨25911265351455548259662861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17274176900970365506441907 25911265351455548259662861)
                  ·
                    refine ⟨9716724506795830597373573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25911265351455548259662861 9716724506795830597373573)
                    ·
                      refine ⟨1821885845024218237007545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9716724506795830597373573 1821885845024218237007545)
                      ·
                        rfl

theorem cell23_3548110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_3548110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3548110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3548110 prefixEnd_3548110 := by exact prefixLift 3548110
  have htrace : WordTrace (prefixWord ++ tailWord_3548110) baseStart_3548110 baseEnd_3548110 := by
    simpa [prefixWord, tailWord_3548110, baseEnd_3548110] using wordTrace_append hprefix tailTrace_3548110
  have hstable : (prefixWord ++ tailWord_3548110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548110).length < 2 ^ (prefixWord ++ tailWord_3548110).sum := by decide
  have hdescent : baseEnd_3548110 < baseStart_3548110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548127 : List Nat := [1, 1, 2, 3, 5, 1, 1, 2, 2, 1, 4]
def baseStart_3548127 : Nat := 118140960795 + 3548127 * 2 ^ 59
def prefixEnd_3548127 : Nat := 4983230072969 + 3 ^ 40 * 3548127 * 2
def baseEnd_3548127 : Nat := 1821894574195344670494967

theorem tailTrace_3548127 : CollatzResearch.WordTrace tailWord_3548127 prefixEnd_3548127 1821894574195344670494967 := by
  unfold tailWord_3548127
  simp only [CollatzResearch.WordTrace]
  refine ⟨129410823216749325692826635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86273882144499550461884423 129410823216749325692826635)
  ·
    refine ⟨194116234825123988539239953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129410823216749325692826635 194116234825123988539239953)
    ·
      refine ⟨145587176118842991404429965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194116234825123988539239953 145587176118842991404429965)
      ·
        refine ⟨54595191044566121776661237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145587176118842991404429965 54595191044566121776661237)
        ·
          refine ⟨5118299160428073916561991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54595191044566121776661237 5118299160428073916561991)
          ·
            refine ⟨7677448740642110874842987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5118299160428073916561991 7677448740642110874842987)
            ·
              refine ⟨11516173110963166312264481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7677448740642110874842987 11516173110963166312264481)
              ·
                refine ⟨8637129833222374734198361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11516173110963166312264481 8637129833222374734198361)
                ·
                  refine ⟨6477847374916781050648771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8637129833222374734198361 6477847374916781050648771)
                  ·
                    refine ⟨9716771062375171575973157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6477847374916781050648771 9716771062375171575973157)
                    ·
                      refine ⟨1821894574195344670494967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9716771062375171575973157 1821894574195344670494967)
                      ·
                        rfl

theorem cell23_3548127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 2, 2, 1, 4].length) (baseStart_3548127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3548127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3548127 prefixEnd_3548127 := by exact prefixLift 3548127
  have htrace : WordTrace (prefixWord ++ tailWord_3548127) baseStart_3548127 baseEnd_3548127 := by
    simpa [prefixWord, tailWord_3548127, baseEnd_3548127] using wordTrace_append hprefix tailTrace_3548127
  have hstable : (prefixWord ++ tailWord_3548127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548127).length < 2 ^ (prefixWord ++ tailWord_3548127).sum := by decide
  have hdescent : baseEnd_3548127 < baseStart_3548127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548188 : List Nat := [2, 2, 3, 1, 4, 2, 2, 2, 1, 4]
def baseStart_3548188 : Nat := 118140960795 + 3548188 * 2 ^ 59
def prefixEnd_3548188 : Nat := 4983230072969 + 3 ^ 40 * 3548188 * 2
def baseEnd_3548188 : Nat := 607308632171756310610729

theorem tailTrace_3548188 : CollatzResearch.WordTrace tailWord_3548188 prefixEnd_3548188 607308632171756310610729 := by
  unfold tailWord_3548188
  simp only [CollatzResearch.WordTrace]
  refine ⟨64706524034764166555398609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86275365379685555407198145 64706524034764166555398609)
  ·
    refine ⟨48529893026073124916548957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64706524034764166555398609 48529893026073124916548957)
    ·
      refine ⟨18198709884777421843705859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48529893026073124916548957 18198709884777421843705859)
      ·
        refine ⟨27298064827166132765558789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18198709884777421843705859 27298064827166132765558789)
        ·
          refine ⟨5118387155093649893542273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27298064827166132765558789 5118387155093649893542273)
          ·
            refine ⟨3838790366320237420156705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5118387155093649893542273 3838790366320237420156705)
            ·
              refine ⟨2879092774740178065117529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3838790366320237420156705 2879092774740178065117529)
              ·
                refine ⟨2159319581055133548838147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2879092774740178065117529 2159319581055133548838147)
                ·
                  refine ⟨3238979371582700323257221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2159319581055133548838147 3238979371582700323257221)
                  ·
                    refine ⟨607308632171756310610729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3238979371582700323257221 607308632171756310610729)
                    ·
                      rfl

theorem cell23_3548188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2, 2, 1, 4].length) (baseStart_3548188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3548188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3548188 prefixEnd_3548188 := by exact prefixLift 3548188
  have htrace : WordTrace (prefixWord ++ tailWord_3548188) baseStart_3548188 baseEnd_3548188 := by
    simpa [prefixWord, tailWord_3548188, baseEnd_3548188] using wordTrace_append hprefix tailTrace_3548188
  have hstable : (prefixWord ++ tailWord_3548188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548188).length < 2 ^ (prefixWord ++ tailWord_3548188).sum := by decide
  have hdescent : baseEnd_3548188 < baseStart_3548188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548217 : List Nat := [1, 2, 1, 5, 2, 1, 2, 1, 3, 1, 4]
def baseStart_3548217 : Nat := 118140960795 + 3548217 * 2 ^ 59
def prefixEnd_3548217 : Nat := 4983230072969 + 3 ^ 40 * 3548217 * 2
def baseEnd_3548217 : Nat := 1821940787454249318369553

theorem tailTrace_3548217 : CollatzResearch.WordTrace tailWord_3548217 prefixEnd_3548217 1821940787454249318369553 := by
  unfold tailWord_3548217
  simp only [CollatzResearch.WordTrace]
  refine ⟨129414105786423271063602905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86276070524282180709068603 129414105786423271063602905)
  ·
    refine ⟨97060579339817453297702179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129414105786423271063602905 97060579339817453297702179)
    ·
      refine ⟨145590869009726179946553269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97060579339817453297702179 145590869009726179946553269)
      ·
        refine ⟨13649143969661829369989369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 145590869009726179946553269 13649143969661829369989369)
        ·
          refine ⟨10236857977246372027492027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13649143969661829369989369 10236857977246372027492027)
          ·
            refine ⟨15355286965869558041238041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10236857977246372027492027 15355286965869558041238041)
            ·
              refine ⟨11516465224402168530928531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15355286965869558041238041 11516465224402168530928531)
              ·
                refine ⟨17274697836603252796392797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11516465224402168530928531 17274697836603252796392797)
                ·
                  refine ⟨6478011688726219798647299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17274697836603252796392797 6478011688726219798647299)
                  ·
                    refine ⟨9717017533089329697970949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6478011688726219798647299 9717017533089329697970949)
                    ·
                      refine ⟨1821940787454249318369553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9717017533089329697970949 1821940787454249318369553)
                      ·
                        rfl

theorem cell23_3548217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_3548217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3548217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3548217 prefixEnd_3548217 := by exact prefixLift 3548217
  have htrace : WordTrace (prefixWord ++ tailWord_3548217) baseStart_3548217 baseEnd_3548217 := by
    simpa [prefixWord, tailWord_3548217, baseEnd_3548217] using wordTrace_append hprefix tailTrace_3548217
  have hstable : (prefixWord ++ tailWord_3548217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548217).length < 2 ^ (prefixWord ++ tailWord_3548217).sum := by decide
  have hdescent : baseEnd_3548217 < baseStart_3548217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548221 : List Nat := [1, 4, 1, 3, 1, 4, 1, 1, 2, 3, 2]
def baseStart_3548221 : Nat := 118140960795 + 3548221 * 2 ^ 59
def prefixEnd_3548221 : Nat := 4983230072969 + 3 ^ 40 * 3548221 * 2
def baseEnd_3548221 : Nat := 1821942841376867302719535

theorem tailTrace_3548221 : CollatzResearch.WordTrace tailWord_3548221 prefixEnd_3548221 1821942841376867302719535 := by
  unfold tailWord_3548221
  simp only [CollatzResearch.WordTrace]
  refine ⟨129414251678408779746748517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86276167785605853164499011 129414251678408779746748517)
  ·
    refine ⟨24265172189701646202515347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129414251678408779746748517 24265172189701646202515347)
    ·
      refine ⟨36397758284552469303773021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24265172189701646202515347 36397758284552469303773021)
      ·
        refine ⟨13649159356707175988914883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36397758284552469303773021 13649159356707175988914883)
        ·
          refine ⟨20473739035060763983372325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13649159356707175988914883 20473739035060763983372325)
          ·
            refine ⟨3838826069073893246882311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20473739035060763983372325 3838826069073893246882311)
            ·
              refine ⟨5758239103610839870323467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3838826069073893246882311 5758239103610839870323467)
              ·
                refine ⟨8637358655416259805485201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5758239103610839870323467 8637358655416259805485201)
                ·
                  refine ⟨6478018991562194854113901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8637358655416259805485201 6478018991562194854113901)
                  ·
                    refine ⟨2429257121835823070292713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6478018991562194854113901 2429257121835823070292713)
                    ·
                      refine ⟨1821942841376867302719535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2429257121835823070292713 1821942841376867302719535)
                      ·
                        rfl

theorem cell23_3548221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_3548221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3548221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3548221 prefixEnd_3548221 := by exact prefixLift 3548221
  have htrace : WordTrace (prefixWord ++ tailWord_3548221) baseStart_3548221 baseEnd_3548221 := by
    simpa [prefixWord, tailWord_3548221, baseEnd_3548221] using wordTrace_append hprefix tailTrace_3548221
  have hstable : (prefixWord ++ tailWord_3548221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548221).length < 2 ^ (prefixWord ++ tailWord_3548221).sum := by decide
  have hdescent : baseEnd_3548221 < baseStart_3548221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548234 : List Nat := [3, 1, 2, 1, 1, 2, 6, 1, 1, 1, 4]
def baseStart_3548234 : Nat := 118140960795 + 3548234 * 2 ^ 59
def prefixEnd_3548234 : Nat := 4983230072969 + 3 ^ 40 * 3548234 * 2
def baseEnd_3548234 : Nat := 1821949516625375751856975

theorem tailTrace_3548234 : CollatzResearch.WordTrace tailWord_3548234 prefixEnd_3548234 1821949516625375751856975 := by
  unfold tailWord_3548234
  simp only [CollatzResearch.WordTrace]
  refine ⟨32353681456840420741742939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86276483884907788644647837 32353681456840420741742939)
  ·
    refine ⟨48530522185260631112614409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32353681456840420741742939 48530522185260631112614409)
    ·
      refine ⟨36397891638945473334460807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48530522185260631112614409 36397891638945473334460807)
      ·
        refine ⟨54596837458418210001691211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36397891638945473334460807 54596837458418210001691211)
        ·
          refine ⟨81895256187627315002536817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54596837458418210001691211 81895256187627315002536817)
          ·
            refine ⟨61421442140720486251902613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81895256187627315002536817 61421442140720486251902613)
            ·
              refine ⟨2879130100346272793057935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 61421442140720486251902613 2879130100346272793057935)
              ·
                refine ⟨4318695150519409189586903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2879130100346272793057935 4318695150519409189586903)
                ·
                  refine ⟨6478042725779113784380355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4318695150519409189586903 6478042725779113784380355)
                  ·
                    refine ⟨9717064088668670676570533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6478042725779113784380355 9717064088668670676570533)
                    ·
                      refine ⟨1821949516625375751856975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9717064088668670676570533 1821949516625375751856975)
                      ·
                        rfl

theorem cell23_3548234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6, 1, 1, 1, 4].length) (baseStart_3548234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3548234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3548234 prefixEnd_3548234 := by exact prefixLift 3548234
  have htrace : WordTrace (prefixWord ++ tailWord_3548234) baseStart_3548234 baseEnd_3548234 := by
    simpa [prefixWord, tailWord_3548234, baseEnd_3548234] using wordTrace_append hprefix tailTrace_3548234
  have hstable : (prefixWord ++ tailWord_3548234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548234).length < 2 ^ (prefixWord ++ tailWord_3548234).sum := by decide
  have hdescent : baseEnd_3548234 < baseStart_3548234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548244 : List Nat := [2, 4, 1, 1, 1, 1, 5, 2, 2, 4]
def baseStart_3548244 : Nat := 118140960795 + 3548244 * 2 ^ 59
def prefixEnd_3548244 : Nat := 4983230072969 + 3 ^ 40 * 3548244 * 2
def baseEnd_3548244 : Nat := 607318217143973570910643

theorem tailTrace_3548244 : CollatzResearch.WordTrace tailWord_3548244 prefixEnd_3548244 607318217143973570910643 := by
  unfold tailWord_3548244
  simp only [CollatzResearch.WordTrace]
  refine ⟨64707545278662727337417893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86276727038216969783223857 64707545278662727337417893)
  ·
    refine ⟨12132664739749261375765855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64707545278662727337417893 12132664739749261375765855)
    ·
      refine ⟨18198997109623892063648783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12132664739749261375765855 18198997109623892063648783)
      ·
        refine ⟨27298495664435838095473175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18198997109623892063648783 27298495664435838095473175)
        ·
          refine ⟨40947743496653757143209763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27298495664435838095473175 40947743496653757143209763)
          ·
            refine ⟨61421615244980635714814645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40947743496653757143209763 61421615244980635714814645)
            ·
              refine ⟨5758276429216934598263873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61421615244980635714814645 5758276429216934598263873)
              ·
                refine ⟨4318707321912700948697905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5758276429216934598263873 4318707321912700948697905)
                ·
                  refine ⟨3239030491434525711523429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4318707321912700948697905 3239030491434525711523429)
                  ·
                    refine ⟨607318217143973570910643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3239030491434525711523429 607318217143973570910643)
                    ·
                      rfl

theorem cell23_3548244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_3548244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3548244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3548244 prefixEnd_3548244 := by exact prefixLift 3548244
  have htrace : WordTrace (prefixWord ++ tailWord_3548244) baseStart_3548244 baseEnd_3548244 := by
    simpa [prefixWord, tailWord_3548244, baseEnd_3548244] using wordTrace_append hprefix tailTrace_3548244
  have hstable : (prefixWord ++ tailWord_3548244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548244).length < 2 ^ (prefixWord ++ tailWord_3548244).sum := by decide
  have hdescent : baseEnd_3548244 < baseStart_3548244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548264 : List Nat := [2, 1, 4, 4, 1, 1, 1, 1, 1, 1, 6]
def baseStart_3548264 : Nat := 118140960795 + 3548264 * 2 ^ 59
def prefixEnd_3548264 : Nat := 4983230072969 + 3 ^ 40 * 3548264 * 2
def baseEnd_3548264 : Nat := 1821964921045010634481837

theorem tailTrace_3548264 : CollatzResearch.WordTrace tailWord_3548264 prefixEnd_3548264 1821964921045010634481837 := by
  unfold tailWord_3548264
  simp only [CollatzResearch.WordTrace]
  refine ⟨64707910008626499045281923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86277213344835332060375897 64707910008626499045281923)
  ·
    refine ⟨97061865012939748567922885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64707910008626499045281923 97061865012939748567922885)
    ·
      refine ⟨18199099689926202856485541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97061865012939748567922885 18199099689926202856485541)
      ·
        refine ⟨3412331191861163035591039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18199099689926202856485541 3412331191861163035591039)
        ·
          refine ⟨5118496787791744553386559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3412331191861163035591039 5118496787791744553386559)
          ·
            refine ⟨7677745181687616830079839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5118496787791744553386559 7677745181687616830079839)
            ·
              refine ⟨11516617772531425245119759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7677745181687616830079839 11516617772531425245119759)
              ·
                refine ⟨17274926658797137867679639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11516617772531425245119759 17274926658797137867679639)
                ·
                  refine ⟨25912389988195706801519459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17274926658797137867679639 25912389988195706801519459)
                  ·
                    refine ⟨38868584982293560202279189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25912389988195706801519459 38868584982293560202279189)
                    ·
                      refine ⟨1821964921045010634481837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38868584982293560202279189 1821964921045010634481837)
                      ·
                        rfl

theorem cell23_3548264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_3548264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3548264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3548264 prefixEnd_3548264 := by exact prefixLift 3548264
  have htrace : WordTrace (prefixWord ++ tailWord_3548264) baseStart_3548264 baseEnd_3548264 := by
    simpa [prefixWord, tailWord_3548264, baseEnd_3548264] using wordTrace_append hprefix tailTrace_3548264
  have hstable : (prefixWord ++ tailWord_3548264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548264).length < 2 ^ (prefixWord ++ tailWord_3548264).sum := by decide
  have hdescent : baseEnd_3548264 < baseStart_3548264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548280 : List Nat := [2, 1, 2, 1, 1, 1, 5, 1, 2, 2, 5]
def baseStart_3548280 : Nat := 118140960795 + 3548280 * 2 ^ 59
def prefixEnd_3548280 : Nat := 4983230072969 + 3 ^ 40 * 3548280 * 2
def baseEnd_3548280 : Nat := 1821973136735482571881763

theorem tailTrace_3548280 : CollatzResearch.WordTrace tailWord_3548280 prefixEnd_3548280 1821973136735482571881763 := by
  unfold tailWord_3548280
  simp only [CollatzResearch.WordTrace]
  refine ⟨64708201792597516411573147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86277602390130021882097529 64708201792597516411573147)
  ·
    refine ⟨97062302688896274617359721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64708201792597516411573147 97062302688896274617359721)
    ·
      refine ⟨72796727016672205963019791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97062302688896274617359721 72796727016672205963019791)
      ·
        refine ⟨109195090525008308944529687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72796727016672205963019791 109195090525008308944529687)
        ·
          refine ⟨163792635787512463416794531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109195090525008308944529687 163792635787512463416794531)
          ·
            refine ⟨245688953681268695125191797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163792635787512463416794531 245688953681268695125191797)
            ·
              refine ⟨23033339407618940167986731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 245688953681268695125191797 23033339407618940167986731)
              ·
                refine ⟨34550009111428410251980097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23033339407618940167986731 34550009111428410251980097)
                ·
                  refine ⟨25912506833571307688985073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34550009111428410251980097 25912506833571307688985073)
                  ·
                    refine ⟨19434380125178480766738805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25912506833571307688985073 19434380125178480766738805)
                    ·
                      refine ⟨1821973136735482571881763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19434380125178480766738805 1821973136735482571881763)
                      ·
                        rfl

theorem cell23_3548280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 2, 2, 5].length) (baseStart_3548280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3548280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3548280 prefixEnd_3548280 := by exact prefixLift 3548280
  have htrace : WordTrace (prefixWord ++ tailWord_3548280) baseStart_3548280 baseEnd_3548280 := by
    simpa [prefixWord, tailWord_3548280, baseEnd_3548280] using wordTrace_append hprefix tailTrace_3548280
  have hstable : (prefixWord ++ tailWord_3548280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548280).length < 2 ^ (prefixWord ++ tailWord_3548280).sum := by decide
  have hdescent : baseEnd_3548280 < baseStart_3548280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548300 : List Nat := [2, 2, 1, 2, 1, 1, 1, 3, 4, 6]
def baseStart_3548300 : Nat := 118140960795 + 3548300 * 2 ^ 59
def prefixEnd_3548300 : Nat := 4983230072969 + 3 ^ 40 * 3548300 * 2
def baseEnd_3548300 : Nat := 607327802116190831210557

theorem tailTrace_3548300 : CollatzResearch.WordTrace tailWord_3548300 prefixEnd_3548300 607327802116190831210557 := by
  unfold tailWord_3548300
  simp only [CollatzResearch.WordTrace]
  refine ⟨64708566522561288119437177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86278088696748384159249569 64708566522561288119437177)
  ·
    refine ⟨48531424891920966089577883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64708566522561288119437177 48531424891920966089577883)
    ·
      refine ⟨72797137337881449134366825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48531424891920966089577883 72797137337881449134366825)
      ·
        refine ⟨54597853003411086850775119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72797137337881449134366825 54597853003411086850775119)
        ·
          refine ⟨81896779505116630276162679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54597853003411086850775119 81896779505116630276162679)
          ·
            refine ⟨122845169257674945414244019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81896779505116630276162679 122845169257674945414244019)
            ·
              refine ⟨184267753886512418121366029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122845169257674945414244019 184267753886512418121366029)
              ·
                refine ⟨69100407707442156795512261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 184267753886512418121366029 69100407707442156795512261)
                ·
                  refine ⟨12956326445145404399158549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69100407707442156795512261 12956326445145404399158549)
                  ·
                    refine ⟨607327802116190831210557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12956326445145404399158549 607327802116190831210557)
                    ·
                      rfl

theorem cell23_3548300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 4, 6].length) (baseStart_3548300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3548300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3548300 prefixEnd_3548300 := by exact prefixLift 3548300
  have htrace : WordTrace (prefixWord ++ tailWord_3548300) baseStart_3548300 baseEnd_3548300 := by
    simpa [prefixWord, tailWord_3548300, baseEnd_3548300] using wordTrace_append hprefix tailTrace_3548300
  have hstable : (prefixWord ++ tailWord_3548300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548300).length < 2 ^ (prefixWord ++ tailWord_3548300).sum := by decide
  have hdescent : baseEnd_3548300 < baseStart_3548300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548318 : List Nat := [4, 3, 1, 1, 2, 2, 1, 3, 2, 1, 3]
def baseStart_3548318 : Nat := 118140960795 + 3548318 * 2 ^ 59
def prefixEnd_3548318 : Nat := 4983230072969 + 3 ^ 40 * 3548318 * 2
def baseEnd_3548318 : Nat := 1821992649000353423206589

theorem tailTrace_3548318 : CollatzResearch.WordTrace tailWord_3548318 prefixEnd_3548318 1821992649000353423206589 := by
  unfold tailWord_3548318
  simp only [CollatzResearch.WordTrace]
  refine ⟨16177223694882170664128701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86278526372704910208686405 16177223694882170664128701)
  ·
    refine ⟨6066458885580813999048263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16177223694882170664128701 6066458885580813999048263)
    ·
      refine ⟨9099688328371220998572395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6066458885580813999048263 9099688328371220998572395)
      ·
        refine ⟨13649532492556831497858593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9099688328371220998572395 13649532492556831497858593)
        ·
          refine ⟨10237149369417623623393945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13649532492556831497858593 10237149369417623623393945)
          ·
            refine ⟨7677862027063217717545459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10237149369417623623393945 7677862027063217717545459)
            ·
              refine ⟨11516793040594826576318189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7677862027063217717545459 11516793040594826576318189)
              ·
                refine ⟨4318797390223059966119321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11516793040594826576318189 4318797390223059966119321)
                ·
                  refine ⟨3239098042667294974589491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4318797390223059966119321 3239098042667294974589491)
                  ·
                    refine ⟨4858647064000942461884237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3239098042667294974589491 4858647064000942461884237)
                    ·
                      refine ⟨1821992649000353423206589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4858647064000942461884237 1821992649000353423206589)
                      ·
                        rfl

theorem cell23_3548318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_3548318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3548318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3548318 prefixEnd_3548318 := by exact prefixLift 3548318
  have htrace : WordTrace (prefixWord ++ tailWord_3548318) baseStart_3548318 baseEnd_3548318 := by
    simpa [prefixWord, tailWord_3548318, baseEnd_3548318] using wordTrace_append hprefix tailTrace_3548318
  have hstable : (prefixWord ++ tailWord_3548318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548318).length < 2 ^ (prefixWord ++ tailWord_3548318).sum := by decide
  have hdescent : baseEnd_3548318 < baseStart_3548318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548357 : List Nat := [1, 3, 1, 1, 1, 1, 3, 4, 2, 3, 3]
def baseStart_3548357 : Nat := 118140960795 + 3548357 * 2 ^ 59
def prefixEnd_3548357 : Nat := 4983230072969 + 3 ^ 40 * 3548357 * 2
def baseEnd_3548357 : Nat := 1822012674745878770618909

theorem tailTrace_3548357 : CollatzResearch.WordTrace tailWord_3548357 prefixEnd_3548357 1822012674745878770618909 := by
  unfold tailWord_3548357
  simp only [CollatzResearch.WordTrace]
  refine ⟨129419212005916074973699325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86279474670610716649132883 129419212005916074973699325)
  ·
    refine ⟨48532204502218528115137247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129419212005916074973699325 48532204502218528115137247)
    ·
      refine ⟨72798306753327792172705871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48532204502218528115137247 72798306753327792172705871)
      ·
        refine ⟨109197460129991688259058807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72798306753327792172705871 109197460129991688259058807)
        ·
          refine ⟨163796190194987532388588211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109197460129991688259058807 163796190194987532388588211)
          ·
            refine ⟨245694285292481298582882317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163796190194987532388588211 245694285292481298582882317)
            ·
              refine ⟨92135356984680486968580869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 245694285292481298582882317 92135356984680486968580869)
              ·
                refine ⟨17275379434627591306608913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92135356984680486968580869 17275379434627591306608913)
                ·
                  refine ⟨12956534575970693479956685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17275379434627591306608913 12956534575970693479956685)
                  ·
                    refine ⟨4858700465989010054983757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12956534575970693479956685 4858700465989010054983757)
                    ·
                      refine ⟨1822012674745878770618909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4858700465989010054983757 1822012674745878770618909)
                      ·
                        rfl

theorem cell23_3548357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 2, 3, 3].length) (baseStart_3548357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3548357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3548357 prefixEnd_3548357 := by exact prefixLift 3548357
  have htrace : WordTrace (prefixWord ++ tailWord_3548357) baseStart_3548357 baseEnd_3548357 := by
    simpa [prefixWord, tailWord_3548357, baseEnd_3548357] using wordTrace_append hprefix tailTrace_3548357
  have hstable : (prefixWord ++ tailWord_3548357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548357).length < 2 ^ (prefixWord ++ tailWord_3548357).sum := by decide
  have hdescent : baseEnd_3548357 < baseStart_3548357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548394 : List Nat := [3, 1, 3, 1, 1, 3, 3, 1, 2, 5]
def baseStart_3548394 : Nat := 118140960795 + 3548394 * 2 ^ 59
def prefixEnd_3548394 : Nat := 4983230072969 + 3 ^ 40 * 3548394 * 2
def baseEnd_3548394 : Nat := 607343891176698375285413

theorem tailTrace_3548394 : CollatzResearch.WordTrace tailWord_3548394 prefixEnd_3548394 607343891176698375285413 := by
  unfold tailWord_3548394
  simp only [CollatzResearch.WordTrace]
  refine ⟨32355140376695507573199059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86280374337854686861864157 32355140376695507573199059)
  ·
    refine ⟨48532710565043261359798589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32355140376695507573199059 48532710565043261359798589)
    ·
      refine ⟨18199766461891223009924471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48532710565043261359798589 18199766461891223009924471)
      ·
        refine ⟨27299649692836834514886707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18199766461891223009924471 27299649692836834514886707)
        ·
          refine ⟨40949474539255251772330061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27299649692836834514886707 40949474539255251772330061)
          ·
            refine ⟨15356052952220719414623773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40949474539255251772330061 15356052952220719414623773)
            ·
              refine ⟨5758519857082769780483915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15356052952220719414623773 5758519857082769780483915)
              ·
                refine ⟨8637779785624154670725873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5758519857082769780483915 8637779785624154670725873)
                ·
                  refine ⟨6478334839218116003044405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8637779785624154670725873 6478334839218116003044405)
                  ·
                    refine ⟨607343891176698375285413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6478334839218116003044405 607343891176698375285413)
                    ·
                      rfl

theorem cell23_3548394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_3548394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3548394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3548394 prefixEnd_3548394 := by exact prefixLift 3548394
  have htrace : WordTrace (prefixWord ++ tailWord_3548394) baseStart_3548394 baseEnd_3548394 := by
    simpa [prefixWord, tailWord_3548394, baseEnd_3548394] using wordTrace_append hprefix tailTrace_3548394
  have hstable : (prefixWord ++ tailWord_3548394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548394).length < 2 ^ (prefixWord ++ tailWord_3548394).sum := by decide
  have hdescent : baseEnd_3548394 < baseStart_3548394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548501 : List Nat := [1, 3, 2, 2, 3, 1, 3, 2, 1, 5]
def baseStart_3548501 : Nat := 118140960795 + 3548501 * 2 ^ 59
def prefixEnd_3548501 : Nat := 4983230072969 + 3 ^ 40 * 3548501 * 2
def baseEnd_3548501 : Nat := 607362205320042069072749

theorem tailTrace_3548501 : CollatzResearch.WordTrace tailWord_3548501 prefixEnd_3548501 607362205320042069072749 := by
  unfold tailWord_3548501
  simp only [CollatzResearch.WordTrace]
  refine ⟨129424464117394387566941357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86282976078262925044627571 129424464117394387566941357)
  ·
    refine ⟨48534174044022895337603009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129424464117394387566941357 48534174044022895337603009)
    ·
      refine ⟨36400630533017171503202257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48534174044022895337603009 36400630533017171503202257)
      ·
        refine ⟨27300472899762878627401693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36400630533017171503202257 27300472899762878627401693)
        ·
          refine ⟨10237677337411079485275635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27300472899762878627401693 10237677337411079485275635)
          ·
            refine ⟨15356516006116619227913453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10237677337411079485275635 15356516006116619227913453)
            ·
              refine ⟨5758693502293732210467545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15356516006116619227913453 5758693502293732210467545)
              ·
                refine ⟨4319020126720299157850659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5758693502293732210467545 4319020126720299157850659)
                ·
                  refine ⟨6478530190080448736775989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4319020126720299157850659 6478530190080448736775989)
                  ·
                    refine ⟨607362205320042069072749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6478530190080448736775989 607362205320042069072749)
                    ·
                      rfl

theorem cell23_3548501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 2, 1, 5].length) (baseStart_3548501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3548501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3548501 prefixEnd_3548501 := by exact prefixLift 3548501
  have htrace : WordTrace (prefixWord ++ tailWord_3548501) baseStart_3548501 baseEnd_3548501 := by
    simpa [prefixWord, tailWord_3548501, baseEnd_3548501] using wordTrace_append hprefix tailTrace_3548501
  have hstable : (prefixWord ++ tailWord_3548501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548501).length < 2 ^ (prefixWord ++ tailWord_3548501).sum := by decide
  have hdescent : baseEnd_3548501 < baseStart_3548501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548504 : List Nat := [2, 1, 2, 2, 1, 1, 5, 1, 3, 1, 4]
def baseStart_3548504 : Nat := 118140960795 + 3548504 * 2 ^ 59
def prefixEnd_3548504 : Nat := 4983230072969 + 3 ^ 40 * 3548504 * 2
def baseEnd_3548504 : Nat := 1822088156402089695480733

theorem tailTrace_3548504 : CollatzResearch.WordTrace tailWord_3548504 prefixEnd_3548504 1822088156402089695480733 := by
  unfold tailWord_3548504
  simp only [CollatzResearch.WordTrace]
  refine ⟨64712286768191759539650283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86283049024255679386200377 64712286768191759539650283)
  ·
    refine ⟨97068430152287639309475425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64712286768191759539650283 97068430152287639309475425)
    ·
      refine ⟨72801322614215729482106569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97068430152287639309475425 72801322614215729482106569)
      ·
        refine ⟨54600991960661797111579927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72801322614215729482106569 54600991960661797111579927)
        ·
          refine ⟨81901487940992695667369891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54600991960661797111579927 81901487940992695667369891)
          ·
            refine ⟨122852231911489043501054837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81901487940992695667369891 122852231911489043501054837)
            ·
              refine ⟨11517396741702097828223891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 122852231911489043501054837 11517396741702097828223891)
              ·
                refine ⟨17276095112553146742335837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11517396741702097828223891 17276095112553146742335837)
                ·
                  refine ⟨6478535667207430028375939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17276095112553146742335837 6478535667207430028375939)
                  ·
                    refine ⟨9717803500811145042563909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6478535667207430028375939 9717803500811145042563909)
                    ·
                      refine ⟨1822088156402089695480733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9717803500811145042563909 1822088156402089695480733)
                      ·
                        rfl

theorem cell23_3548504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 3, 1, 4].length) (baseStart_3548504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3548504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3548504 prefixEnd_3548504 := by exact prefixLift 3548504
  have htrace : WordTrace (prefixWord ++ tailWord_3548504) baseStart_3548504 baseEnd_3548504 := by
    simpa [prefixWord, tailWord_3548504, baseEnd_3548504] using wordTrace_append hprefix tailTrace_3548504
  have hstable : (prefixWord ++ tailWord_3548504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548504).length < 2 ^ (prefixWord ++ tailWord_3548504).sum := by decide
  have hdescent : baseEnd_3548504 < baseStart_3548504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548521 : List Nat := [1, 2, 1, 1, 1, 3, 2, 1, 7, 2, 2]
def baseStart_3548521 : Nat := 118140960795 + 3548521 * 2 ^ 59
def prefixEnd_3548521 : Nat := 4983230072969 + 3 ^ 40 * 3548521 * 2
def baseEnd_3548521 : Nat := 1822096885573216128968155

theorem tailTrace_3548521 : CollatzResearch.WordTrace tailWord_3548521 prefixEnd_3548521 1822096885573216128968155 := by
  unfold tailWord_3548521
  simp only [CollatzResearch.WordTrace]
  refine ⟨129425193577321930982669417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86283462384881287321779611 129425193577321930982669417)
  ·
    refine ⟨97068895182991448237002063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129425193577321930982669417 97068895182991448237002063)
    ·
      refine ⟨145603342774487172355503095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97068895182991448237002063 145603342774487172355503095)
      ·
        refine ⟨218405014161730758533254643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145603342774487172355503095 218405014161730758533254643)
        ·
          refine ⟨327607521242596137799881965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218405014161730758533254643 327607521242596137799881965)
          ·
            refine ⟨122852820465973551674955737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 327607521242596137799881965 122852820465973551674955737)
            ·
              refine ⟨92139615349480163756216803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122852820465973551674955737 92139615349480163756216803)
              ·
                refine ⟨138209423024220245634325205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92139615349480163756216803 138209423024220245634325205)
                ·
                  refine ⟨3239283352130162007054497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 138209423024220245634325205 3239283352130162007054497)
                  ·
                    refine ⟨2429462514097621505290873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3239283352130162007054497 2429462514097621505290873)
                    ·
                      refine ⟨1822096885573216128968155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2429462514097621505290873 1822096885573216128968155)
                      ·
                        rfl

theorem cell23_3548521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 7, 2, 2].length) (baseStart_3548521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3548521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3548521 prefixEnd_3548521 := by exact prefixLift 3548521
  have htrace : WordTrace (prefixWord ++ tailWord_3548521) baseStart_3548521 baseEnd_3548521 := by
    simpa [prefixWord, tailWord_3548521, baseEnd_3548521] using wordTrace_append hprefix tailTrace_3548521
  have hstable : (prefixWord ++ tailWord_3548521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548521).length < 2 ^ (prefixWord ++ tailWord_3548521).sum := by decide
  have hdescent : baseEnd_3548521 < baseStart_3548521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548551 : List Nat := [1, 1, 4, 2, 2, 3, 2, 1, 1, 2, 4]
def baseStart_3548551 : Nat := 118140960795 + 3548551 * 2 ^ 59
def prefixEnd_3548551 : Nat := 4983230072969 + 3 ^ 40 * 3548551 * 2
def baseEnd_3548551 : Nat := 1822112289992851011593017

theorem tailTrace_3548551 : CollatzResearch.WordTrace tailWord_3548551 prefixEnd_3548551 1822112289992851011593017 := by
  unfold tailWord_3548551
  simp only [CollatzResearch.WordTrace]
  refine ⟨129426287767213246106261507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86284191844808830737507671 129426287767213246106261507)
  ·
    refine ⟨194139431650819869159392261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129426287767213246106261507 194139431650819869159392261)
    ·
      refine ⟨36401143434528725467386049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194139431650819869159392261 36401143434528725467386049)
      ·
        refine ⟨27300857575896544100539537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36401143434528725467386049 27300857575896544100539537)
        ·
          refine ⟨20475643181922408075404653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27300857575896544100539537 20475643181922408075404653)
          ·
            refine ⟨7678366193220903028276745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20475643181922408075404653 7678366193220903028276745)
            ·
              refine ⟨5758774644915677271207559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7678366193220903028276745 5758774644915677271207559)
              ·
                refine ⟨8638161967373515906811339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5758774644915677271207559 8638161967373515906811339)
                ·
                  refine ⟨12957242951060273860217009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8638161967373515906811339 12957242951060273860217009)
                  ·
                    refine ⟨9717932213295205395162757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12957242951060273860217009 9717932213295205395162757)
                    ·
                      refine ⟨1822112289992851011593017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9717932213295205395162757 1822112289992851011593017)
                      ·
                        rfl

theorem cell23_3548551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_3548551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3548551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3548551 prefixEnd_3548551 := by exact prefixLift 3548551
  have htrace : WordTrace (prefixWord ++ tailWord_3548551) baseStart_3548551 baseEnd_3548551 := by
    simpa [prefixWord, tailWord_3548551, baseEnd_3548551] using wordTrace_append hprefix tailTrace_3548551
  have hstable : (prefixWord ++ tailWord_3548551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548551).length < 2 ^ (prefixWord ++ tailWord_3548551).sum := by decide
  have hdescent : baseEnd_3548551 < baseStart_3548551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548572 : List Nat := [2, 2, 3, 4, 1, 2, 2, 1, 1, 1, 4]
def baseStart_3548572 : Nat := 118140960795 + 3548572 * 2 ^ 59
def prefixEnd_3548572 : Nat := 4983230072969 + 3 ^ 40 * 3548572 * 2
def baseEnd_3548572 : Nat := 1822123073086595429430421

theorem tailTrace_3548572 : CollatzResearch.WordTrace tailWord_3548572 prefixEnd_3548572 1822123073086595429430421 := by
  unfold tailWord_3548572
  simp only [CollatzResearch.WordTrace]
  refine ⟨64713526850068583346387985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86284702466758111128517313 64713526850068583346387985)
  ·
    refine ⟨48535145137551437509790989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64713526850068583346387985 48535145137551437509790989)
    ·
      refine ⟨18200679426581789066171621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48535145137551437509790989 18200679426581789066171621)
      ·
        refine ⟨3412627392484085449907179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18200679426581789066171621 3412627392484085449907179)
        ·
          refine ⟨5118941088726128174860769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3412627392484085449907179 5118941088726128174860769)
          ·
            refine ⟨3839205816544596131145577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5118941088726128174860769 3839205816544596131145577)
            ·
              refine ⟨2879404362408447098359183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3839205816544596131145577 2879404362408447098359183)
              ·
                refine ⟨4319106543612670647538775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2879404362408447098359183 4319106543612670647538775)
                ·
                  refine ⟨6478659815419005971308163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4319106543612670647538775 6478659815419005971308163)
                  ·
                    refine ⟨9717989723128508956962245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6478659815419005971308163 9717989723128508956962245)
                    ·
                      refine ⟨1822123073086595429430421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9717989723128508956962245 1822123073086595429430421)
                      ·
                        rfl

theorem cell23_3548572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_3548572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3548572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3548572 prefixEnd_3548572 := by exact prefixLift 3548572
  have htrace : WordTrace (prefixWord ++ tailWord_3548572) baseStart_3548572 baseEnd_3548572 := by
    simpa [prefixWord, tailWord_3548572, baseEnd_3548572] using wordTrace_append hprefix tailTrace_3548572
  have hstable : (prefixWord ++ tailWord_3548572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548572).length < 2 ^ (prefixWord ++ tailWord_3548572).sum := by decide
  have hdescent : baseEnd_3548572 < baseStart_3548572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548575 : List Nat := [1, 1, 2, 5, 1, 4, 2, 1, 1, 2, 3]
def baseStart_3548575 : Nat := 118140960795 + 3548575 * 2 ^ 59
def prefixEnd_3548575 : Nat := 4983230072969 + 3 ^ 40 * 3548575 * 2
def baseEnd_3548575 : Nat := 1822124613528558917692907

theorem tailTrace_3548575 : CollatzResearch.WordTrace tailWord_3548575 prefixEnd_3548575 1822124613528558917692907 := by
  unfold tailWord_3548575
  simp only [CollatzResearch.WordTrace]
  refine ⟨129427163119126298205135179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86284775412750865470090119 129427163119126298205135179)
  ·
    refine ⟨194140744678689447307702769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129427163119126298205135179 194140744678689447307702769)
    ·
      refine ⟨145605558509017085480777077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194140744678689447307702769 145605558509017085480777077)
      ·
        refine ⟨13650521110220351763822851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 145605558509017085480777077 13650521110220351763822851)
        ·
          refine ⟨20475781665330527645734277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13650521110220351763822851 20475781665330527645734277)
          ·
            refine ⟨3839209062249473933575177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20475781665330527645734277 3839209062249473933575177)
            ·
              refine ⟨2879406796687105450181383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3839209062249473933575177 2879406796687105450181383)
              ·
                refine ⟨4319110195030658175272075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2879406796687105450181383 4319110195030658175272075)
                ·
                  refine ⟨6478665292545987262908113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4319110195030658175272075 6478665292545987262908113)
                  ·
                    refine ⟨4858998969409490447181085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6478665292545987262908113 4858998969409490447181085)
                    ·
                      refine ⟨1822124613528558917692907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4858998969409490447181085 1822124613528558917692907)
                      ·
                        rfl

theorem cell23_3548575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_3548575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3548575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3548575 prefixEnd_3548575 := by exact prefixLift 3548575
  have htrace : WordTrace (prefixWord ++ tailWord_3548575) baseStart_3548575 baseEnd_3548575 := by
    simpa [prefixWord, tailWord_3548575, baseEnd_3548575] using wordTrace_append hprefix tailTrace_3548575
  have hstable : (prefixWord ++ tailWord_3548575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548575).length < 2 ^ (prefixWord ++ tailWord_3548575).sum := by decide
  have hdescent : baseEnd_3548575 < baseStart_3548575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548581 : List Nat := [1, 3, 1, 2, 1, 1, 2, 2, 5, 3, 2]
def baseStart_3548581 : Nat := 118140960795 + 3548581 * 2 ^ 59
def prefixEnd_3548581 : Nat := 4983230072969 + 3 ^ 40 * 3548581 * 2
def baseEnd_3548581 : Nat := 1822127694412485894217879

theorem tailTrace_3548581 : CollatzResearch.WordTrace tailWord_3548581 prefixEnd_3548581 1822127694412485894217879 := by
  unfold tailWord_3548581
  simp only [CollatzResearch.WordTrace]
  refine ⟨129427381957104561229853597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86284921304736374153235731 129427381957104561229853597)
  ·
    refine ⟨48535268233914210461195099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129427381957104561229853597 48535268233914210461195099)
    ·
      refine ⟨72802902350871315691792649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48535268233914210461195099 72802902350871315691792649)
      ·
        refine ⟨54602176763153486768844487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72802902350871315691792649 54602176763153486768844487)
        ·
          refine ⟨81903265144730230153266731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54602176763153486768844487 81903265144730230153266731)
          ·
            refine ⟨122854897717095345229900097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81903265144730230153266731 122854897717095345229900097)
            ·
              refine ⟨92141173287821508922425073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122854897717095345229900097 92141173287821508922425073)
              ·
                refine ⟨69105879965866131691818805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92141173287821508922425073 69105879965866131691818805)
                ·
                  refine ⟨6478676246799949846108013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69105879965866131691818805 6478676246799949846108013)
                  ·
                    refine ⟨2429503592549981192290505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6478676246799949846108013 2429503592549981192290505)
                    ·
                      refine ⟨1822127694412485894217879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2429503592549981192290505 1822127694412485894217879)
                      ·
                        rfl

theorem cell23_3548581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 5, 3, 2].length) (baseStart_3548581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3548581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3548581 prefixEnd_3548581 := by exact prefixLift 3548581
  have htrace : WordTrace (prefixWord ++ tailWord_3548581) baseStart_3548581 baseEnd_3548581 := by
    simpa [prefixWord, tailWord_3548581, baseEnd_3548581] using wordTrace_append hprefix tailTrace_3548581
  have hstable : (prefixWord ++ tailWord_3548581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548581).length < 2 ^ (prefixWord ++ tailWord_3548581).sum := by decide
  have hdescent : baseEnd_3548581 < baseStart_3548581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548588 : List Nat := [2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 3]
def baseStart_3548588 : Nat := 118140960795 + 3548588 * 2 ^ 59
def prefixEnd_3548588 : Nat := 4983230072969 + 3 ^ 40 * 3548588 * 2
def baseEnd_3548588 : Nat := 1822131288777067366830347

theorem tailTrace_3548588 : CollatzResearch.WordTrace tailWord_3548588 prefixEnd_3548588 1822131288777067366830347 := by
  unfold tailWord_3548588
  simp only [CollatzResearch.WordTrace]
  refine ⟨64713818634039600712679209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86285091512052800950238945 64713818634039600712679209)
  ·
    refine ⟨48535363975529700534509407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64713818634039600712679209 48535363975529700534509407)
    ·
      refine ⟨72803045963294550801764111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48535363975529700534509407 72803045963294550801764111)
      ·
        refine ⟨109204568944941826202646167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72803045963294550801764111 109204568944941826202646167)
        ·
          refine ⟨163806853417412739303969251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109204568944941826202646167 163806853417412739303969251)
          ·
            refine ⟨245710280126119108955953877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163806853417412739303969251 245710280126119108955953877)
            ·
              refine ⟨5758834690455916616155169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 245710280126119108955953877 5758834690455916616155169)
              ·
                refine ⟨4319126017841937462116377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5758834690455916616155169 4319126017841937462116377)
                ·
                  refine ⟨3239344513381453096587283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4319126017841937462116377 3239344513381453096587283)
                  ·
                    refine ⟨4859016770072179644880925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3239344513381453096587283 4859016770072179644880925)
                    ·
                      refine ⟨1822131288777067366830347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4859016770072179644880925 1822131288777067366830347)
                      ·
                        rfl

theorem cell23_3548588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 3].length) (baseStart_3548588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3548588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3548588 prefixEnd_3548588 := by exact prefixLift 3548588
  have htrace : WordTrace (prefixWord ++ tailWord_3548588) baseStart_3548588 baseEnd_3548588 := by
    simpa [prefixWord, tailWord_3548588, baseEnd_3548588] using wordTrace_append hprefix tailTrace_3548588
  have hstable : (prefixWord ++ tailWord_3548588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548588).length < 2 ^ (prefixWord ++ tailWord_3548588).sum := by decide
  have hdescent : baseEnd_3548588 < baseStart_3548588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548594 : List Nat := [3, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4]
def baseStart_3548594 : Nat := 118140960795 + 3548594 * 2 ^ 59
def prefixEnd_3548594 : Nat := 4983230072969 + 3 ^ 40 * 3548594 * 2
def baseEnd_3548594 : Nat := 1822134369660994343355319

theorem tailTrace_3548594 : CollatzResearch.WordTrace tailWord_3548594 prefixEnd_3548594 1822134369660994343355319 := by
  unfold tailWord_3548594
  simp only [CollatzResearch.WordTrace]
  refine ⟨32356964026514366112519209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86285237404038309633384557 32356964026514366112519209)
  ·
    refine ⟨24267723019885774584389407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32356964026514366112519209 24267723019885774584389407)
    ·
      refine ⟨36401584529828661876584111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24267723019885774584389407 36401584529828661876584111)
      ·
        refine ⟨54602376794742992814876167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36401584529828661876584111 54602376794742992814876167)
        ·
          refine ⟨81903565192114489222314251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54602376794742992814876167 81903565192114489222314251)
          ·
            refine ⟨122855347788171733833471377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81903565192114489222314251 122855347788171733833471377)
            ·
              refine ⟨92141510841128800375103533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122855347788171733833471377 92141510841128800375103533)
              ·
                refine ⟨34553066565423300140663825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92141510841128800375103533 34553066565423300140663825)
                ·
                  refine ⟨25914799924067475105497869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34553066565423300140663825 25914799924067475105497869)
                  ·
                    refine ⟨9718049971525303164561701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25914799924067475105497869 9718049971525303164561701)
                    ·
                      refine ⟨1822134369660994343355319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9718049971525303164561701 1822134369660994343355319)
                      ·
                        rfl

theorem cell23_3548594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_3548594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3548594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3548594 prefixEnd_3548594 := by exact prefixLift 3548594
  have htrace : WordTrace (prefixWord ++ tailWord_3548594) baseStart_3548594 baseEnd_3548594 := by
    simpa [prefixWord, tailWord_3548594, baseEnd_3548594] using wordTrace_append hprefix tailTrace_3548594
  have hstable : (prefixWord ++ tailWord_3548594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548594).length < 2 ^ (prefixWord ++ tailWord_3548594).sum := by decide
  have hdescent : baseEnd_3548594 < baseStart_3548594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548605 : List Nat := [1, 4, 1, 2, 2, 1, 5, 1, 2, 1, 3]
def baseStart_3548605 : Nat := 118140960795 + 3548605 * 2 ^ 59
def prefixEnd_3548605 : Nat := 4983230072969 + 3 ^ 40 * 3548605 * 2
def baseEnd_3548605 : Nat := 1822140017948193800317769

theorem tailTrace_3548605 : CollatzResearch.WordTrace tailWord_3548605 prefixEnd_3548605 1822140017948193800317769 := by
  unfold tailWord_3548605
  simp only [CollatzResearch.WordTrace]
  refine ⟨129428257309017613328727269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86285504872678408885818179 129428257309017613328727269)
  ·
    refine ⟨24267798245440802499136363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129428257309017613328727269 24267798245440802499136363)
    ·
      refine ⟨36401697368161203748704545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24267798245440802499136363 36401697368161203748704545)
      ·
        refine ⟨27301273026120902811528409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36401697368161203748704545 27301273026120902811528409)
        ·
          refine ⟨20475954769590677108646307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27301273026120902811528409 20475954769590677108646307)
          ·
            refine ⟨30713932154386015662969461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20475954769590677108646307 30713932154386015662969461)
            ·
              refine ⟨2879431139473688968403387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30713932154386015662969461 2879431139473688968403387)
              ·
                refine ⟨4319146709210533452605081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2879431139473688968403387 4319146709210533452605081)
                ·
                  refine ⟨3239360031907900089453811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4319146709210533452605081 3239360031907900089453811)
                  ·
                    refine ⟨4859040047861850134180717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3239360031907900089453811 4859040047861850134180717)
                    ·
                      refine ⟨1822140017948193800317769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4859040047861850134180717 1822140017948193800317769)
                      ·
                        rfl

theorem cell23_3548605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5, 1, 2, 1, 3].length) (baseStart_3548605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3548605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3548605 prefixEnd_3548605 := by exact prefixLift 3548605
  have htrace : WordTrace (prefixWord ++ tailWord_3548605) baseStart_3548605 baseEnd_3548605 := by
    simpa [prefixWord, tailWord_3548605, baseEnd_3548605] using wordTrace_append hprefix tailTrace_3548605
  have hstable : (prefixWord ++ tailWord_3548605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548605).length < 2 ^ (prefixWord ++ tailWord_3548605).sum := by decide
  have hdescent : baseEnd_3548605 < baseStart_3548605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548645 : List Nat := [1, 3, 1, 5, 1, 1, 2, 1, 4, 2, 2]
def baseStart_3548645 : Nat := 118140960795 + 3548645 * 2 ^ 59
def prefixEnd_3548645 : Nat := 4983230072969 + 3 ^ 40 * 3548645 * 2
def baseEnd_3548645 : Nat := 1822160557174373643817585

theorem tailTrace_3548645 : CollatzResearch.WordTrace tailWord_3548645 prefixEnd_3548645 1822160557174373643817585 := by
  unfold tailWord_3548645
  simp only [CollatzResearch.WordTrace]
  refine ⟨129429716228872700160183389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86286477485915133440122259 129429716228872700160183389)
  ·
    refine ⟨48536143585827262560068771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129429716228872700160183389 48536143585827262560068771)
    ·
      refine ⟨72804215378740893840103157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48536143585827262560068771 72804215378740893840103157)
      ·
        refine ⟨6825395191756958797509671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72804215378740893840103157 6825395191756958797509671)
        ·
          refine ⟨10238092787635438196264507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6825395191756958797509671 10238092787635438196264507)
          ·
            refine ⟨15357139181453157294396761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10238092787635438196264507 15357139181453157294396761)
            ·
              refine ⟨11517854386089867970797571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15357139181453157294396761 11517854386089867970797571)
              ·
                refine ⟨17276781579134801956196357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11517854386089867970797571 17276781579134801956196357)
                ·
                  refine ⟨3239396546087775366786817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17276781579134801956196357 3239396546087775366786817)
                  ·
                    refine ⟨2429547409565831525090113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3239396546087775366786817 2429547409565831525090113)
                    ·
                      refine ⟨1822160557174373643817585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2429547409565831525090113 1822160557174373643817585)
                      ·
                        rfl

theorem cell23_3548645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_3548645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3548645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3548645 prefixEnd_3548645 := by exact prefixLift 3548645
  have htrace : WordTrace (prefixWord ++ tailWord_3548645) baseStart_3548645 baseEnd_3548645 := by
    simpa [prefixWord, tailWord_3548645, baseEnd_3548645] using wordTrace_append hprefix tailTrace_3548645
  have hstable : (prefixWord ++ tailWord_3548645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548645).length < 2 ^ (prefixWord ++ tailWord_3548645).sum := by decide
  have hdescent : baseEnd_3548645 < baseStart_3548645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548662 : List Nat := [5, 1, 1, 1, 2, 3, 1, 3, 2, 2, 2]
def baseStart_3548662 : Nat := 118140960795 + 3548662 * 2 ^ 59
def prefixEnd_3548662 : Nat := 4983230072969 + 3 ^ 40 * 3548662 * 2
def baseEnd_3548662 : Nat := 1822169286345500077305007

theorem tailTrace_3548662 : CollatzResearch.WordTrace tailWord_3548662 prefixEnd_3548662 1822169286345500077305007 := by
  unfold tailWord_3548662
  simp only [CollatzResearch.WordTrace]
  refine ⟨8089396016863194503972015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86286890846540741375701493 8089396016863194503972015)
  ·
    refine ⟨12134094025294791755958023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8089396016863194503972015 12134094025294791755958023)
    ·
      refine ⟨18201141037942187633937035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12134094025294791755958023 18201141037942187633937035)
      ·
        refine ⟨27301711556913281450905553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18201141037942187633937035 27301711556913281450905553)
        ·
          refine ⟨20476283667684961088179165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27301711556913281450905553 20476283667684961088179165)
          ·
            refine ⟨7678606375381860408067187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20476283667684961088179165 7678606375381860408067187)
            ·
              refine ⟨11517909563072790612100781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7678606375381860408067187 11517909563072790612100781)
              ·
                refine ⟨4319216086152296479537793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11517909563072790612100781 4319216086152296479537793)
                ·
                  refine ⟨3239412064614222359653345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4319216086152296479537793 3239412064614222359653345)
                  ·
                    refine ⟨2429559048460666769740009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3239412064614222359653345 2429559048460666769740009)
                    ·
                      refine ⟨1822169286345500077305007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2429559048460666769740009 1822169286345500077305007)
                      ·
                        rfl

theorem cell23_3548662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 3, 2, 2, 2].length) (baseStart_3548662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3548662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3548662 prefixEnd_3548662 := by exact prefixLift 3548662
  have htrace : WordTrace (prefixWord ++ tailWord_3548662) baseStart_3548662 baseEnd_3548662 := by
    simpa [prefixWord, tailWord_3548662, baseEnd_3548662] using wordTrace_append hprefix tailTrace_3548662
  have hstable : (prefixWord ++ tailWord_3548662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548662).length < 2 ^ (prefixWord ++ tailWord_3548662).sum := by decide
  have hdescent : baseEnd_3548662 < baseStart_3548662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548671 : List Nat := [1, 1, 2, 2, 1, 2, 2, 1, 4, 5, 2]
def baseStart_3548671 : Nat := 118140960795 + 3548671 * 2 ^ 59
def prefixEnd_3548671 : Nat := 4983230072969 + 3 ^ 40 * 3548671 * 2
def baseEnd_3548671 : Nat := 1822173907671390542092465

theorem tailTrace_3548671 : CollatzResearch.WordTrace tailWord_3548671 prefixEnd_3548671 1822173907671390542092465 := by
  unfold tailWord_3548671
  simp only [CollatzResearch.WordTrace]
  refine ⟨129430664526778506600629867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86287109684519004400419911 129430664526778506600629867)
  ·
    refine ⟨194145996790167759900944801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129430664526778506600629867 194145996790167759900944801)
    ·
      refine ⟨145609497592625819925708601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194145996790167759900944801 145609497592625819925708601)
      ·
        refine ⟨109207123194469364944281451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145609497592625819925708601 109207123194469364944281451)
        ·
          refine ⟨163810684791704047416422177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109207123194469364944281451 163810684791704047416422177)
          ·
            refine ⟨122858013593778035562316633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163810684791704047416422177 122858013593778035562316633)
            ·
              refine ⟨92143510195333526671737475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122858013593778035562316633 92143510195333526671737475)
              ·
                refine ⟨138215265293000290007606213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92143510195333526671737475 138215265293000290007606213)
                ·
                  refine ⟨25915362242437554376426165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 138215265293000290007606213 25915362242437554376426165)
                  ·
                    refine ⟨2429565210228520722789953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25915362242437554376426165 2429565210228520722789953)
                    ·
                      refine ⟨1822173907671390542092465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2429565210228520722789953 1822173907671390542092465)
                      ·
                        rfl

theorem cell23_3548671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 5, 2].length) (baseStart_3548671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3548671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3548671 prefixEnd_3548671 := by exact prefixLift 3548671
  have htrace : WordTrace (prefixWord ++ tailWord_3548671) baseStart_3548671 baseEnd_3548671 := by
    simpa [prefixWord, tailWord_3548671, baseEnd_3548671] using wordTrace_append hprefix tailTrace_3548671
  have hstable : (prefixWord ++ tailWord_3548671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548671).length < 2 ^ (prefixWord ++ tailWord_3548671).sum := by decide
  have hdescent : baseEnd_3548671 < baseStart_3548671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548681 : List Nat := [1, 2, 1, 1, 3, 1, 6, 1, 2, 5]
def baseStart_3548681 : Nat := 118140960795 + 3548681 * 2 ^ 59
def prefixEnd_3548681 : Nat := 4983230072969 + 3 ^ 40 * 3548681 * 2
def baseEnd_3548681 : Nat := 607393014159311834322473

theorem tailTrace_3548681 : CollatzResearch.WordTrace tailWord_3548681 prefixEnd_3548681 607393014159311834322473 := by
  unfold tailWord_3548681
  simp only [CollatzResearch.WordTrace]
  refine ⟨129431029256742278308493897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86287352837828185538995931 129431029256742278308493897)
  ·
    refine ⟨97073271942556708731370423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129431029256742278308493897 97073271942556708731370423)
    ·
      refine ⟨145609907913835063097055635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97073271942556708731370423 145609907913835063097055635)
      ·
        refine ⟨218414861870752594645583453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145609907913835063097055635 218414861870752594645583453)
        ·
          refine ⟨81905573201532222992093795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218414861870752594645583453 81905573201532222992093795)
          ·
            refine ⟨122858359802298334488140693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81905573201532222992093795 122858359802298334488140693)
            ·
              refine ⟨5758985615732734429131595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 122858359802298334488140693 5758985615732734429131595)
              ·
                refine ⟨8638478423599101643697393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5758985615732734429131595 8638478423599101643697393)
                ·
                  refine ⟨6478858817699326232773045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8638478423599101643697393 6478858817699326232773045)
                  ·
                    refine ⟨607393014159311834322473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6478858817699326232773045 607393014159311834322473)
                    ·
                      rfl

theorem cell23_3548681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 1, 2, 5].length) (baseStart_3548681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3548681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3548681 prefixEnd_3548681 := by exact prefixLift 3548681
  have htrace : WordTrace (prefixWord ++ tailWord_3548681) baseStart_3548681 baseEnd_3548681 := by
    simpa [prefixWord, tailWord_3548681, baseEnd_3548681] using wordTrace_append hprefix tailTrace_3548681
  have hstable : (prefixWord ++ tailWord_3548681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548681).length < 2 ^ (prefixWord ++ tailWord_3548681).sum := by decide
  have hdescent : baseEnd_3548681 < baseStart_3548681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548721 : List Nat := [1, 2, 2, 3, 1, 1, 1, 4, 1, 4, 3]
def baseStart_3548721 : Nat := 118140960795 + 3548721 * 2 ^ 59
def prefixEnd_3548721 : Nat := 4983230072969 + 3 ^ 40 * 3548721 * 2
def baseEnd_3548721 : Nat := 1822199581704115346467235

theorem tailTrace_3548721 : CollatzResearch.WordTrace tailWord_3548721 prefixEnd_3548721 1822199581704115346467235 := by
  unfold tailWord_3548721
  simp only [CollatzResearch.WordTrace]
  refine ⟨129432488176597365139950017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86288325451064910093300011 129432488176597365139950017)
  ·
    refine ⟨97074366132448023854962513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129432488176597365139950017 97074366132448023854962513)
    ·
      refine ⟨72805774599336017891221885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97074366132448023854962513 72805774599336017891221885)
      ·
        refine ⟨27302165474751006709208207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72805774599336017891221885 27302165474751006709208207)
        ·
          refine ⟨40953248212126510063812311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27302165474751006709208207 40953248212126510063812311)
          ·
            refine ⟨61429872318189765095718467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40953248212126510063812311 61429872318189765095718467)
            ·
              refine ⟨92144808477284647643577701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61429872318189765095718467 92144808477284647643577701)
              ·
                refine ⟨17277151589490871433170819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92144808477284647643577701 17277151589490871433170819)
                ·
                  refine ⟨25915727384236307149756229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17277151589490871433170819 25915727384236307149756229)
                  ·
                    refine ⟨4859198884544307590579293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25915727384236307149756229 4859198884544307590579293)
                    ·
                      refine ⟨1822199581704115346467235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4859198884544307590579293 1822199581704115346467235)
                      ·
                        rfl

theorem cell23_3548721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_3548721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3548721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3548721 prefixEnd_3548721 := by exact prefixLift 3548721
  have htrace : WordTrace (prefixWord ++ tailWord_3548721) baseStart_3548721 baseEnd_3548721 := by
    simpa [prefixWord, tailWord_3548721, baseEnd_3548721] using wordTrace_append hprefix tailTrace_3548721
  have hstable : (prefixWord ++ tailWord_3548721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548721).length < 2 ^ (prefixWord ++ tailWord_3548721).sum := by decide
  have hdescent : baseEnd_3548721 < baseStart_3548721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548728 : List Nat := [2, 1, 2, 1, 4, 3, 1, 2, 3, 4]
def baseStart_3548728 : Nat := 118140960795 + 3548728 * 2 ^ 59
def prefixEnd_3548728 : Nat := 4983230072969 + 3 ^ 40 * 3548728 * 2
def baseEnd_3548728 : Nat := 607401058689565606359901

theorem tailTrace_3548728 : CollatzResearch.WordTrace tailWord_3548728 prefixEnd_3548728 607401058689565606359901 := by
  unfold tailWord_3548728
  simp only [CollatzResearch.WordTrace]
  refine ⟨64716371743786002667727419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86288495658381336890303225 64716371743786002667727419)
  ·
    refine ⟨97074557615679004001591129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64716371743786002667727419 97074557615679004001591129)
    ·
      refine ⟨72805918211759253001193347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97074557615679004001591129 72805918211759253001193347)
      ·
        refine ⟨109208877317638879501790021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72805918211759253001193347 109208877317638879501790021)
        ·
          refine ⟨20476664497057289906585629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109208877317638879501790021 20476664497057289906585629)
          ·
            refine ⟨7678749186396483714969611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20476664497057289906585629 7678749186396483714969611)
            ·
              refine ⟨11518123779594725572454417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7678749186396483714969611 11518123779594725572454417)
              ·
                refine ⟨8638592834696044179340813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11518123779594725572454417 8638592834696044179340813)
                ·
                  refine ⟨3239472313011016567252805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8638592834696044179340813 3239472313011016567252805)
                  ·
                    refine ⟨607401058689565606359901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3239472313011016567252805 607401058689565606359901)
                    ·
                      rfl

theorem cell23_3548728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 2, 3, 4].length) (baseStart_3548728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3548728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3548728 prefixEnd_3548728 := by exact prefixLift 3548728
  have htrace : WordTrace (prefixWord ++ tailWord_3548728) baseStart_3548728 baseEnd_3548728 := by
    simpa [prefixWord, tailWord_3548728, baseEnd_3548728] using wordTrace_append hprefix tailTrace_3548728
  have hstable : (prefixWord ++ tailWord_3548728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548728).length < 2 ^ (prefixWord ++ tailWord_3548728).sum := by decide
  have hdescent : baseEnd_3548728 < baseStart_3548728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548825 : List Nat := [1, 2, 1, 2, 1, 2, 2, 5, 3, 2, 2]
def baseStart_3548825 : Nat := 118140960795 + 3548825 * 2 ^ 59
def prefixEnd_3548825 : Nat := 4983230072969 + 3 ^ 40 * 3548825 * 2
def baseEnd_3548825 : Nat := 1822252983692182939566757

theorem tailTrace_3548825 : CollatzResearch.WordTrace tailWord_3548825 prefixEnd_3548825 1822252983692182939566757 := by
  unfold tailWord_3548825
  simp only [CollatzResearch.WordTrace]
  refine ⟨129436281368220590901735929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86290854245480393934490619 129436281368220590901735929)
  ·
    refine ⟨97077211026165443176301947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129436281368220590901735929 97077211026165443176301947)
    ·
      refine ⟨145615816539248164764452921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97077211026165443176301947 145615816539248164764452921)
      ·
        refine ⟨109211862404436123573339691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145615816539248164764452921 109211862404436123573339691)
        ·
          refine ⟨163817793606654185360009537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109211862404436123573339691 163817793606654185360009537)
          ·
            refine ⟨122863345204990639020007153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163817793606654185360009537 122863345204990639020007153)
            ·
              refine ⟨92147508903742979265005365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122863345204990639020007153 92147508903742979265005365)
              ·
                refine ⟨8638828959725904306094253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92147508903742979265005365 8638828959725904306094253)
                ·
                  refine ⟨3239560859897214114785345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8638828959725904306094253 3239560859897214114785345)
                  ·
                    refine ⟨2429670644922910586089009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3239560859897214114785345 2429670644922910586089009)
                    ·
                      refine ⟨1822252983692182939566757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2429670644922910586089009 1822252983692182939566757)
                      ·
                        rfl

theorem cell23_3548825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5, 3, 2, 2].length) (baseStart_3548825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3548825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3548825 prefixEnd_3548825 := by exact prefixLift 3548825
  have htrace : WordTrace (prefixWord ++ tailWord_3548825) baseStart_3548825 baseEnd_3548825 := by
    simpa [prefixWord, tailWord_3548825, baseEnd_3548825] using wordTrace_append hprefix tailTrace_3548825
  have hstable : (prefixWord ++ tailWord_3548825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548825).length < 2 ^ (prefixWord ++ tailWord_3548825).sum := by decide
  have hdescent : baseEnd_3548825 < baseStart_3548825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548845 : List Nat := [1, 5, 2, 1, 1, 1, 3, 1, 3, 2, 3]
def baseStart_3548845 : Nat := 118140960795 + 3548845 * 2 ^ 59
def prefixEnd_3548845 : Nat := 4983230072969 + 3 ^ 40 * 3548845 * 2
def baseEnd_3548845 : Nat := 1822263253305272861316665

theorem tailTrace_3548845 : CollatzResearch.WordTrace tailWord_3548845 prefixEnd_3548845 1822263253305272861316665 := by
  unfold tailWord_3548845
  simp only [CollatzResearch.WordTrace]
  refine ⟨129437010828148134317463989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86291340552098756211642659 129437010828148134317463989)
  ·
    refine ⟨12134719765138887592262249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 129437010828148134317463989 12134719765138887592262249)
    ·
      refine ⟨9101039823854165694196687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12134719765138887592262249 9101039823854165694196687)
      ·
        refine ⟨13651559735781248541295031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9101039823854165694196687 13651559735781248541295031)
        ·
          refine ⟨20477339603671872811942547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13651559735781248541295031 20477339603671872811942547)
          ·
            refine ⟨30716009405507809217913821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20477339603671872811942547 30716009405507809217913821)
            ·
              refine ⟨11518503527065428456717683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30716009405507809217913821 11518503527065428456717683)
              ·
                refine ⟨17277755290598142685076525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11518503527065428456717683 17277755290598142685076525)
                ·
                  refine ⟨6479158233974303506903697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17277755290598142685076525 6479158233974303506903697)
                  ·
                    refine ⟨4859368675480727630177773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6479158233974303506903697 4859368675480727630177773)
                    ·
                      refine ⟨1822263253305272861316665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4859368675480727630177773 1822263253305272861316665)
                      ·
                        rfl

theorem cell23_3548845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_3548845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3548845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3548845 prefixEnd_3548845 := by exact prefixLift 3548845
  have htrace : WordTrace (prefixWord ++ tailWord_3548845) baseStart_3548845 baseEnd_3548845 := by
    simpa [prefixWord, tailWord_3548845, baseEnd_3548845] using wordTrace_append hprefix tailTrace_3548845
  have hstable : (prefixWord ++ tailWord_3548845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548845).length < 2 ^ (prefixWord ++ tailWord_3548845).sum := by decide
  have hdescent : baseEnd_3548845 < baseStart_3548845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548858 : List Nat := [3, 1, 1, 1, 2, 4, 1, 1, 3, 3, 3]
def baseStart_3548858 : Nat := 118140960795 + 3548858 * 2 ^ 59
def prefixEnd_3548858 : Nat := 4983230072969 + 3 ^ 40 * 3548858 * 2
def baseEnd_3548858 : Nat := 1822269928553781310454105

theorem tailTrace_3548858 : CollatzResearch.WordTrace tailWord_3548858 prefixEnd_3548858 1822269928553781310454105 := by
  unfold tailWord_3548858
  simp only [CollatzResearch.WordTrace]
  refine ⟨32359371244275259384421807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86291656651400691691791485 32359371244275259384421807)
  ·
    refine ⟨48539056866412889076632711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32359371244275259384421807 48539056866412889076632711)
    ·
      refine ⟨72808585299619333614949067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48539056866412889076632711 72808585299619333614949067)
      ·
        refine ⟨109212877949429000422423601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72808585299619333614949067 109212877949429000422423601)
        ·
          refine ⟨81909658462071750316817701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109212877949429000422423601 81909658462071750316817701)
          ·
            refine ⟨15358060961638453184403319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81909658462071750316817701 15358060961638453184403319)
            ·
              refine ⟨23037091442457679776604979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15358060961638453184403319 23037091442457679776604979)
              ·
                refine ⟨34555637163686519664907469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23037091442457679776604979 34555637163686519664907469)
                ·
                  refine ⟨12958363936382444874340301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34555637163686519664907469 12958363936382444874340301)
                  ·
                    refine ⟨4859386476143416827877613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12958363936382444874340301 4859386476143416827877613)
                    ·
                      refine ⟨1822269928553781310454105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4859386476143416827877613 1822269928553781310454105)
                      ·
                        rfl

theorem cell23_3548858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 3, 3, 3].length) (baseStart_3548858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3548858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3548858 prefixEnd_3548858 := by exact prefixLift 3548858
  have htrace : WordTrace (prefixWord ++ tailWord_3548858) baseStart_3548858 baseEnd_3548858 := by
    simpa [prefixWord, tailWord_3548858, baseEnd_3548858] using wordTrace_append hprefix tailTrace_3548858
  have hstable : (prefixWord ++ tailWord_3548858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548858).length < 2 ^ (prefixWord ++ tailWord_3548858).sum := by decide
  have hdescent : baseEnd_3548858 < baseStart_3548858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548870 : List Nat := [6, 1, 2, 1, 1, 3, 2, 2, 1, 1, 3]
def baseStart_3548870 : Nat := 118140960795 + 3548870 * 2 ^ 59
def prefixEnd_3548870 : Nat := 4983230072969 + 3 ^ 40 * 3548870 * 2
def baseEnd_3548870 : Nat := 1822276090321635263504051

theorem tailTrace_3548870 : CollatzResearch.WordTrace tailWord_3548870 prefixEnd_3548870 1822276090321635263504051 := by
  unfold tailWord_3548870
  simp only [CollatzResearch.WordTrace]
  refine ⟨4044935082908048862097627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 86291948435371709058082709 4044935082908048862097627)
  ·
    refine ⟨6067402624362073293146441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4044935082908048862097627 6067402624362073293146441)
    ·
      refine ⟨4550551968271554969859831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6067402624362073293146441 4550551968271554969859831)
      ·
        refine ⟨6825827952407332454789747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4550551968271554969859831 6825827952407332454789747)
        ·
          refine ⟨10238741928610998682184621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6825827952407332454789747 10238741928610998682184621)
          ·
            refine ⟨3839528223229124505819233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10238741928610998682184621 3839528223229124505819233)
            ·
              refine ⟨2879646167421843379364425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3839528223229124505819233 2879646167421843379364425)
              ·
                refine ⟨2159734625566382534523319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2879646167421843379364425 2159734625566382534523319)
                ·
                  refine ⟨3239601938349573801784979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2159734625566382534523319 3239601938349573801784979)
                  ·
                    refine ⟨4859402907524360702677469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3239601938349573801784979 4859402907524360702677469)
                    ·
                      refine ⟨1822276090321635263504051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4859402907524360702677469 1822276090321635263504051)
                      ·
                        rfl

theorem cell23_3548870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_3548870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3548870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3548870 prefixEnd_3548870 := by exact prefixLift 3548870
  have htrace : WordTrace (prefixWord ++ tailWord_3548870) baseStart_3548870 baseEnd_3548870 := by
    simpa [prefixWord, tailWord_3548870, baseEnd_3548870] using wordTrace_append hprefix tailTrace_3548870
  have hstable : (prefixWord ++ tailWord_3548870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548870).length < 2 ^ (prefixWord ++ tailWord_3548870).sum := by decide
  have hdescent : baseEnd_3548870 < baseStart_3548870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548876 : List Nat := [2, 2, 1, 5, 2, 1, 1, 4, 1, 2, 2]
def baseStart_3548876 : Nat := 118140960795 + 3548876 * 2 ^ 59
def prefixEnd_3548876 : Nat := 4983230072969 + 3 ^ 40 * 3548876 * 2
def baseEnd_3548876 : Nat := 1822279171205562240029023

theorem tailTrace_3548876 : CollatzResearch.WordTrace tailWord_3548876 prefixEnd_3548876 1822279171205562240029023 := by
  unfold tailWord_3548876
  simp only [CollatzResearch.WordTrace]
  refine ⟨64719070745517913305921241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86292094327357217741228321 64719070745517913305921241)
  ·
    refine ⟨48539303059138434979440931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64719070745517913305921241 48539303059138434979440931)
    ·
      refine ⟨72808954588707652469161397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48539303059138434979440931 72808954588707652469161397)
      ·
        refine ⟨6825839492691342418983881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72808954588707652469161397 6825839492691342418983881)
        ·
          refine ⟨5119379619518506814237911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6825839492691342418983881 5119379619518506814237911)
          ·
            refine ⟨7679069429277760221356867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5119379619518506814237911 7679069429277760221356867)
            ·
              refine ⟨11518604143916640332035301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7679069429277760221356867 11518604143916640332035301)
              ·
                refine ⟨2159738276984370062256619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11518604143916640332035301 2159738276984370062256619)
                ·
                  refine ⟨3239607415476555093384929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2159738276984370062256619 3239607415476555093384929)
                  ·
                    refine ⟨2429705561607416320038697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3239607415476555093384929 2429705561607416320038697)
                    ·
                      refine ⟨1822279171205562240029023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2429705561607416320038697 1822279171205562240029023)
                      ·
                        rfl

theorem cell23_3548876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_3548876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3548876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3548876 prefixEnd_3548876 := by exact prefixLift 3548876
  have htrace : WordTrace (prefixWord ++ tailWord_3548876) baseStart_3548876 baseEnd_3548876 := by
    simpa [prefixWord, tailWord_3548876, baseEnd_3548876] using wordTrace_append hprefix tailTrace_3548876
  have hstable : (prefixWord ++ tailWord_3548876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548876).length < 2 ^ (prefixWord ++ tailWord_3548876).sum := by decide
  have hdescent : baseEnd_3548876 < baseStart_3548876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548915 : List Nat := [1, 1, 1, 2, 2, 3, 4, 2, 1, 4, 2]
def baseStart_3548915 : Nat := 118140960795 + 3548915 * 2 ^ 59
def prefixEnd_3548915 : Nat := 4983230072969 + 3 ^ 40 * 3548915 * 2
def baseEnd_3548915 : Nat := 1822299196951087587441343

theorem tailTrace_3548915 : CollatzResearch.WordTrace tailWord_3548915 prefixEnd_3548915 1822299196951087587441343 := by
  unfold tailWord_3548915
  simp only [CollatzResearch.WordTrace]
  refine ⟨129439563937894536272512199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86293042625263024181674799 129439563937894536272512199)
  ·
    refine ⟨194159345906841804408768299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129439563937894536272512199 194159345906841804408768299)
    ·
      refine ⟨291239018860262706613152449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194159345906841804408768299 291239018860262706613152449)
      ·
        refine ⟨218429264145197029959864337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291239018860262706613152449 218429264145197029959864337)
        ·
          refine ⟨163821948108897772469898253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218429264145197029959864337 163821948108897772469898253)
          ·
            refine ⟨61433230540836664676211845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163821948108897772469898253 61433230540836664676211845)
            ·
              refine ⟨11518730726406874626789721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61433230540836664676211845 11518730726406874626789721)
              ·
                refine ⟨8639048044805155970092291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11518730726406874626789721 8639048044805155970092291)
                ·
                  refine ⟨12958572067207733955138437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8639048044805155970092291 12958572067207733955138437)
                  ·
                    refine ⟨2429732262601450116588457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12958572067207733955138437 2429732262601450116588457)
                    ·
                      refine ⟨1822299196951087587441343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2429732262601450116588457 1822299196951087587441343)
                      ·
                        rfl

theorem cell23_3548915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2, 1, 4, 2].length) (baseStart_3548915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3548915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3548915 prefixEnd_3548915 := by exact prefixLift 3548915
  have htrace : WordTrace (prefixWord ++ tailWord_3548915) baseStart_3548915 baseEnd_3548915 := by
    simpa [prefixWord, tailWord_3548915, baseEnd_3548915] using wordTrace_append hprefix tailTrace_3548915
  have hstable : (prefixWord ++ tailWord_3548915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548915).length < 2 ^ (prefixWord ++ tailWord_3548915).sum := by decide
  have hdescent : baseEnd_3548915 < baseStart_3548915 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548926 : List Nat := [4, 2, 2, 1, 3, 2, 1, 2, 2, 1, 3]
def baseStart_3548926 : Nat := 118140960795 + 3548926 * 2 ^ 59
def prefixEnd_3548926 : Nat := 4983230072969 + 3 ^ 40 * 3548926 * 2
def baseEnd_3548926 : Nat := 1822304845238287044403793

theorem tailTrace_3548926 : CollatzResearch.WordTrace tailWord_3548926 prefixEnd_3548926 1822304845238287044403793 := by
  unfold tailWord_3548926
  simp only [CollatzResearch.WordTrace]
  refine ⟨16179995642606835643895329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86293310093903123434108421 16179995642606835643895329)
  ·
    refine ⟨12134996731955126732921497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16179995642606835643895329 12134996731955126732921497)
    ·
      refine ⟨9101247548966345049691123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12134996731955126732921497 9101247548966345049691123)
      ·
        refine ⟨13651871323449517574536685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9101247548966345049691123 13651871323449517574536685)
        ·
          refine ⟨5119451746293569090451257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13651871323449517574536685 5119451746293569090451257)
          ·
            refine ⟨3839588809720176817838443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5119451746293569090451257 3839588809720176817838443)
            ·
              refine ⟨5759383214580265226757665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3839588809720176817838443 5759383214580265226757665)
              ·
                refine ⟨4319537410935198920068249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5759383214580265226757665 4319537410935198920068249)
                ·
                  refine ⟨3239653058201399190051187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4319537410935198920068249 3239653058201399190051187)
                  ·
                    refine ⟨4859479587302098785076781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3239653058201399190051187 4859479587302098785076781)
                    ·
                      refine ⟨1822304845238287044403793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4859479587302098785076781 1822304845238287044403793)
                      ·
                        rfl

theorem cell23_3548926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_3548926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3548926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3548926 prefixEnd_3548926 := by exact prefixLift 3548926
  have htrace : WordTrace (prefixWord ++ tailWord_3548926) baseStart_3548926 baseEnd_3548926 := by
    simpa [prefixWord, tailWord_3548926, baseEnd_3548926] using wordTrace_append hprefix tailTrace_3548926
  have hstable : (prefixWord ++ tailWord_3548926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548926).length < 2 ^ (prefixWord ++ tailWord_3548926).sum := by decide
  have hdescent : baseEnd_3548926 < baseStart_3548926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548938 : List Nat := [3, 1, 2, 2, 1, 3, 1, 3, 7]
def baseStart_3548938 : Nat := 118140960795 + 3548938 * 2 ^ 59
def prefixEnd_3548938 : Nat := 4983230072969 + 3 ^ 40 * 3548938 * 2
def baseEnd_3548938 : Nat := 202479000778460110828193

theorem tailTrace_3548938 : CollatzResearch.WordTrace tailWord_3548938 prefixEnd_3548938 202479000778460110828193 := by
  unfold tailWord_3548938
  simp only [CollatzResearch.WordTrace]
  refine ⟨32360100704202802800149867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86293601877874140800399645 32360100704202802800149867)
  ·
    refine ⟨48540151056304204200224801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32360100704202802800149867 48540151056304204200224801)
    ·
      refine ⟨36405113292228153150168601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48540151056304204200224801 36405113292228153150168601)
      ·
        refine ⟨27303834969171114862626451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36405113292228153150168601 27303834969171114862626451)
        ·
          refine ⟨40955752453756672293939677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27303834969171114862626451 40955752453756672293939677)
          ·
            refine ⟨15358407170158752110227379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40955752453756672293939677 15358407170158752110227379)
            ·
              refine ⟨23037610755238128165341069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15358407170158752110227379 23037610755238128165341069)
              ·
                refine ⟨8639104033214298062002901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23037610755238128165341069 8639104033214298062002901)
                ·
                  refine ⟨202479000778460110828193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8639104033214298062002901 202479000778460110828193)
                  ·
                    rfl

theorem cell23_3548938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 3, 7].length) (baseStart_3548938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3548938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3548938 prefixEnd_3548938 := by exact prefixLift 3548938
  have htrace : WordTrace (prefixWord ++ tailWord_3548938) baseStart_3548938 baseEnd_3548938 := by
    simpa [prefixWord, tailWord_3548938, baseEnd_3548938] using wordTrace_append hprefix tailTrace_3548938
  have hstable : (prefixWord ++ tailWord_3548938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548938).length < 2 ^ (prefixWord ++ tailWord_3548938).sum := by decide
  have hdescent : baseEnd_3548938 < baseStart_3548938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548972 : List Nat := [2, 2, 1, 1, 1, 7, 1, 3, 5]
def baseStart_3548972 : Nat := 118140960795 + 3548972 * 2 ^ 59
def prefixEnd_3548972 : Nat := 4983230072969 + 3 ^ 40 * 3548972 * 2
def baseEnd_3548972 : Nat := 202480940594265984936509

theorem tailTrace_3548972 : CollatzResearch.WordTrace tailWord_3548972 prefixEnd_3548972 202480940594265984936509 := by
  unfold tailWord_3548972
  simp only [CollatzResearch.WordTrace]
  refine ⟨64720821449344017503668585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86294428599125356671558113 64720821449344017503668585)
  ·
    refine ⟨48540616087008013127751439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64720821449344017503668585 48540616087008013127751439)
    ·
      refine ⟨72810924130512019691627159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48540616087008013127751439 72810924130512019691627159)
      ·
        refine ⟨109216386195768029537440739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72810924130512019691627159 109216386195768029537440739)
        ·
          refine ⟨163824579293652044306161109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109216386195768029537440739 163824579293652044306161109)
          ·
            refine ⟨3839638577194969788425651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 163824579293652044306161109 3839638577194969788425651)
            ·
              refine ⟨5759457865792454682638477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3839638577194969788425651 5759457865792454682638477)
              ·
                refine ⟨2159796699672170505989429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5759457865792454682638477 2159796699672170505989429)
                ·
                  refine ⟨202480940594265984936509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2159796699672170505989429 202480940594265984936509)
                  ·
                    rfl

theorem cell23_3548972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 3, 5].length) (baseStart_3548972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3548972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3548972 prefixEnd_3548972 := by exact prefixLift 3548972
  have htrace : WordTrace (prefixWord ++ tailWord_3548972) baseStart_3548972 baseEnd_3548972 := by
    simpa [prefixWord, tailWord_3548972, baseEnd_3548972] using wordTrace_append hprefix tailTrace_3548972
  have hstable : (prefixWord ++ tailWord_3548972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548972).length < 2 ^ (prefixWord ++ tailWord_3548972).sum := by decide
  have hdescent : baseEnd_3548972 < baseStart_3548972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3548989 : List Nat := [1, 4, 1, 4, 1, 2, 3, 2, 5]
def baseStart_3548989 : Nat := 118140960795 + 3548989 * 2 ^ 59
def prefixEnd_3548989 : Nat := 4983230072969 + 3 ^ 40 * 3548989 * 2
def baseEnd_3548989 : Nat := 202481910502168921990667

theorem tailTrace_3548989 : CollatzResearch.WordTrace tailWord_3548989 prefixEnd_3548989 202481910502168921990667 := by
  unfold tailWord_3548989
  simp only [CollatzResearch.WordTrace]
  refine ⟨129442262939626446910706021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86294841959750964607137347 129442262939626446910706021)
  ·
    refine ⟨24270424301179958795757379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129442262939626446910706021 24270424301179958795757379)
    ·
      refine ⟨36405636451769938193636069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24270424301179958795757379 36405636451769938193636069)
      ·
        refine ⟨6826056834706863411306763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36405636451769938193636069 6826056834706863411306763)
        ·
          refine ⟨10239085252060295116960145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6826056834706863411306763 10239085252060295116960145)
          ·
            refine ⟨7679313939045221337720109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10239085252060295116960145 7679313939045221337720109)
            ·
              refine ⟨2879742727141958001645041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7679313939045221337720109 2879742727141958001645041)
              ·
                refine ⟨2159807045356468501233781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2879742727141958001645041 2159807045356468501233781)
                ·
                  refine ⟨202481910502168921990667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2159807045356468501233781 202481910502168921990667)
                  ·
                    rfl

theorem cell23_3548989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3, 2, 5].length) (baseStart_3548989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3548989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3548989 prefixEnd_3548989 := by exact prefixLift 3548989
  have htrace : WordTrace (prefixWord ++ tailWord_3548989) baseStart_3548989 baseEnd_3548989 := by
    simpa [prefixWord, tailWord_3548989, baseEnd_3548989] using wordTrace_append hprefix tailTrace_3548989
  have hstable : (prefixWord ++ tailWord_3548989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3548989).length < 2 ^ (prefixWord ++ tailWord_3548989).sum := by decide
  have hdescent : baseEnd_3548989 < baseStart_3548989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3548989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549068 : List Nat := [2, 2, 1, 2, 1, 2, 1, 1, 1, 3, 7]
def baseStart_3549068 : Nat := 118140960795 + 3549068 * 2 ^ 59
def prefixEnd_3549068 : Nat := 4983230072969 + 3 ^ 40 * 3549068 * 2
def baseEnd_3549068 : Nat := 1822377759491225488828139

theorem tailTrace_3549068 : CollatzResearch.WordTrace tailWord_3549068 prefixEnd_3549068 1822377759491225488828139 := by
  unfold tailWord_3549068
  simp only [CollatzResearch.WordTrace]
  refine ⟨64722572153170121701415929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86296762870893495601887905 64722572153170121701415929)
  ·
    refine ⟨48541929114877591276061947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64722572153170121701415929 48541929114877591276061947)
    ·
      refine ⟨72812893672316386914092921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48541929114877591276061947 72812893672316386914092921)
      ·
        refine ⟨54609670254237290185569691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72812893672316386914092921 54609670254237290185569691)
        ·
          refine ⟨81914505381355935278354537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54609670254237290185569691 81914505381355935278354537)
          ·
            refine ⟨61435879036016951458765903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81914505381355935278354537 61435879036016951458765903)
            ·
              refine ⟨92153818554025427188148855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61435879036016951458765903 92153818554025427188148855)
              ·
                refine ⟨138230727831038140782223283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92153818554025427188148855 138230727831038140782223283)
                ·
                  refine ⟨207346091746557211173334925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138230727831038140782223283 207346091746557211173334925)
                  ·
                    refine ⟨77754784404958954190000597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 207346091746557211173334925 77754784404958954190000597)
                    ·
                      refine ⟨1822377759491225488828139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 77754784404958954190000597 1822377759491225488828139)
                      ·
                        rfl

theorem cell23_3549068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_3549068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3549068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3549068 prefixEnd_3549068 := by exact prefixLift 3549068
  have htrace : WordTrace (prefixWord ++ tailWord_3549068) baseStart_3549068 baseEnd_3549068 := by
    simpa [prefixWord, tailWord_3549068, baseEnd_3549068] using wordTrace_append hprefix tailTrace_3549068
  have hstable : (prefixWord ++ tailWord_3549068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549068).length < 2 ^ (prefixWord ++ tailWord_3549068).sum := by decide
  have hdescent : baseEnd_3549068 < baseStart_3549068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549092 : List Nat := [2, 3, 1, 2, 1, 4, 1, 3, 1, 5]
def baseStart_3549092 : Nat := 118140960795 + 3549092 * 2 ^ 59
def prefixEnd_3549092 : Nat := 4983230072969 + 3 ^ 40 * 3549092 * 2
def baseEnd_3549092 : Nat := 607463361008977798309343

theorem tailTrace_3549092 : CollatzResearch.WordTrace tailWord_3549092 prefixEnd_3549092 607463361008977798309343 := by
  unfold tailWord_3549092
  simp only [CollatzResearch.WordTrace]
  refine ⟨64723009829126647750852765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86297346438835530334470353 64723009829126647750852765)
  ·
    refine ⟨24271128685922492906569787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64723009829126647750852765 24271128685922492906569787)
    ·
      refine ⟨36406693028883739359854681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24271128685922492906569787 36406693028883739359854681)
      ·
        refine ⟨27305019771662804519891011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36406693028883739359854681 27305019771662804519891011)
        ·
          refine ⟨40957529657494206779836517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27305019771662804519891011 40957529657494206779836517)
          ·
            refine ⟨7679536810780163771219347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40957529657494206779836517 7679536810780163771219347)
            ·
              refine ⟨11519305216170245656829021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7679536810780163771219347 11519305216170245656829021)
              ·
                refine ⟨4319739456063842121310883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11519305216170245656829021 4319739456063842121310883)
                ·
                  refine ⟨6479609184095763181966325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4319739456063842121310883 6479609184095763181966325)
                  ·
                    refine ⟨607463361008977798309343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6479609184095763181966325 607463361008977798309343)
                    ·
                      rfl

theorem cell23_3549092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 3, 1, 5].length) (baseStart_3549092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3549092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3549092 prefixEnd_3549092 := by exact prefixLift 3549092
  have htrace : WordTrace (prefixWord ++ tailWord_3549092) baseStart_3549092 baseEnd_3549092 := by
    simpa [prefixWord, tailWord_3549092, baseEnd_3549092] using wordTrace_append hprefix tailTrace_3549092
  have hstable : (prefixWord ++ tailWord_3549092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549092).length < 2 ^ (prefixWord ++ tailWord_3549092).sum := by decide
  have hdescent : baseEnd_3549092 < baseStart_3549092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549096 : List Nat := [2, 1, 6, 2, 1, 2, 1, 2, 6]
def baseStart_3549096 : Nat := 118140960795 + 3549096 * 2 ^ 59
def prefixEnd_3549096 : Nat := 4983230072969 + 3 ^ 40 * 3549096 * 2
def baseEnd_3549096 : Nat := 202488015216616819919779

theorem tailTrace_3549096 : CollatzResearch.WordTrace tailWord_3549096 prefixEnd_3549096 202488015216616819919779 := by
  unfold tailWord_3549096
  simp only [CollatzResearch.WordTrace]
  refine ⟨64723082775119402092425571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86297443700159202789900761 64723082775119402092425571)
  ·
    refine ⟨97084624162679103138638357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64723082775119402092425571 97084624162679103138638357)
    ·
      refine ⟨4550841757625582959623673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 97084624162679103138638357 4550841757625582959623673)
      ·
        refine ⟨3413131318219187219717755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4550841757625582959623673 3413131318219187219717755)
        ·
          refine ⟨5119696977328780829576633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3413131318219187219717755 5119696977328780829576633)
          ·
            refine ⟨3839772732996585622182475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5119696977328780829576633 3839772732996585622182475)
            ·
              refine ⟨5759659099494878433273713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3839772732996585622182475 5759659099494878433273713)
              ·
                refine ⟨4319744324621158824955285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5759659099494878433273713 4319744324621158824955285)
                ·
                  refine ⟨202488015216616819919779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4319744324621158824955285 202488015216616819919779)
                  ·
                    rfl

theorem cell23_3549096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 2, 6].length) (baseStart_3549096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3549096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3549096 prefixEnd_3549096 := by exact prefixLift 3549096
  have htrace : WordTrace (prefixWord ++ tailWord_3549096) baseStart_3549096 baseEnd_3549096 := by
    simpa [prefixWord, tailWord_3549096, baseEnd_3549096] using wordTrace_append hprefix tailTrace_3549096
  have hstable : (prefixWord ++ tailWord_3549096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549096).length < 2 ^ (prefixWord ++ tailWord_3549096).sum := by decide
  have hdescent : baseEnd_3549096 < baseStart_3549096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549125 : List Nat := [1, 3, 1, 1, 1, 1, 1, 7, 1, 2, 4]
def baseStart_3549125 : Nat := 118140960795 + 3549125 * 2 ^ 59
def prefixEnd_3549125 : Nat := 4983230072969 + 3 ^ 40 * 3549125 * 2
def baseEnd_3549125 : Nat := 1822407027888531765815377

theorem tailTrace_3549125 : CollatzResearch.WordTrace tailWord_3549125 prefixEnd_3549125 1822407027888531765815377 := by
  unfold tailWord_3549125
  simp only [CollatzResearch.WordTrace]
  refine ⟨129447223267133742137656829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86298148844755828091771219 129447223267133742137656829)
  ·
    refine ⟨48542708725175153301621311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129447223267133742137656829 48542708725175153301621311)
    ·
      refine ⟨72814063087762729952431967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48542708725175153301621311 72814063087762729952431967)
      ·
        refine ⟨109221094631644094928647951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72814063087762729952431967 109221094631644094928647951)
        ·
          refine ⟨163831641947466142392971927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109221094631644094928647951 163831641947466142392971927)
          ·
            refine ⟨245747462921199213589457891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163831641947466142392971927 245747462921199213589457891)
            ·
              refine ⟨368621194381798820384186837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245747462921199213589457891 368621194381798820384186837)
              ·
                refine ⟨8639559243323409852754379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 368621194381798820384186837 8639559243323409852754379)
                ·
                  refine ⟨12959338864985114779131569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8639559243323409852754379 12959338864985114779131569)
                  ·
                    refine ⟨9719504148738836084348677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12959338864985114779131569 9719504148738836084348677)
                    ·
                      refine ⟨1822407027888531765815377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9719504148738836084348677 1822407027888531765815377)
                      ·
                        rfl

theorem cell23_3549125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7, 1, 2, 4].length) (baseStart_3549125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3549125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3549125 prefixEnd_3549125 := by exact prefixLift 3549125
  have htrace : WordTrace (prefixWord ++ tailWord_3549125) baseStart_3549125 baseEnd_3549125 := by
    simpa [prefixWord, tailWord_3549125, baseEnd_3549125] using wordTrace_append hprefix tailTrace_3549125
  have hstable : (prefixWord ++ tailWord_3549125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549125).length < 2 ^ (prefixWord ++ tailWord_3549125).sum := by decide
  have hdescent : baseEnd_3549125 < baseStart_3549125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549149 : List Nat := [1, 4, 3, 1, 3, 1, 2, 1, 1, 1, 5]
def baseStart_3549149 : Nat := 118140960795 + 3549149 * 2 ^ 59
def prefixEnd_3549149 : Nat := 4983230072969 + 3 ^ 40 * 3549149 * 2
def baseEnd_3549149 : Nat := 1822419351424239671915267

theorem tailTrace_3549149 : CollatzResearch.WordTrace tailWord_3549149 prefixEnd_3549149 1822419351424239671915267 := by
  unfold tailWord_3549149
  simp only [CollatzResearch.WordTrace]
  refine ⟨129448098619046794236530501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86298732412697862824353667 129448098619046794236530501)
  ·
    refine ⟨24271518491071273919349469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129448098619046794236530501 24271518491071273919349469)
    ·
      refine ⟨9101819434151727719756051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24271518491071273919349469 9101819434151727719756051)
      ·
        refine ⟨13652729151227591579634077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9101819434151727719756051 13652729151227591579634077)
        ·
          refine ⟨5119773431710346842362779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13652729151227591579634077 5119773431710346842362779)
          ·
            refine ⟨7679660147565520263544169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5119773431710346842362779 7679660147565520263544169)
            ·
              refine ⟨5759745110674140197658127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7679660147565520263544169 5759745110674140197658127)
              ·
                refine ⟨8639617666011210296487191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5759745110674140197658127 8639617666011210296487191)
                ·
                  refine ⟨12959426499016815444730787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8639617666011210296487191 12959426499016815444730787)
                  ·
                    refine ⟨19439139748525223167096181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12959426499016815444730787 19439139748525223167096181)
                    ·
                      refine ⟨1822419351424239671915267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19439139748525223167096181 1822419351424239671915267)
                      ·
                        rfl

theorem cell23_3549149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_3549149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3549149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3549149 prefixEnd_3549149 := by exact prefixLift 3549149
  have htrace : WordTrace (prefixWord ++ tailWord_3549149) baseStart_3549149 baseEnd_3549149 := by
    simpa [prefixWord, tailWord_3549149, baseEnd_3549149] using wordTrace_append hprefix tailTrace_3549149
  have hstable : (prefixWord ++ tailWord_3549149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549149).length < 2 ^ (prefixWord ++ tailWord_3549149).sum := by decide
  have hdescent : baseEnd_3549149 < baseStart_3549149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549189 : List Nat := [1, 3, 1, 1, 2, 5, 1, 1, 3, 3, 2]
def baseStart_3549189 : Nat := 118140960795 + 3549189 * 2 ^ 59
def prefixEnd_3549189 : Nat := 4983230072969 + 3 ^ 40 * 3549189 * 2
def baseEnd_3549189 : Nat := 1822439890650419515415083

theorem tailTrace_3549189 : CollatzResearch.WordTrace tailWord_3549189 prefixEnd_3549189 1822439890650419515415083 := by
  unfold tailWord_3549189
  simp only [CollatzResearch.WordTrace]
  refine ⟨129449557538901881067986621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86299705025934587378657747 129449557538901881067986621)
  ·
    refine ⟨48543584077088205400494983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129449557538901881067986621 48543584077088205400494983)
    ·
      refine ⟨72815376115632308100742475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48543584077088205400494983 72815376115632308100742475)
      ·
        refine ⟨109223064173448462151113713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72815376115632308100742475 109223064173448462151113713)
        ·
          refine ⟨81917298130086346613335285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109223064173448462151113713 81917298130086346613335285)
          ·
            refine ⟨7679746699695594995000183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81917298130086346613335285 7679746699695594995000183)
            ·
              refine ⟨11519620049543392492500275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7679746699695594995000183 11519620049543392492500275)
              ·
                refine ⟨17279430074315088738750413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11519620049543392492500275 17279430074315088738750413)
                ·
                  refine ⟨6479786277868158277031405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17279430074315088738750413 6479786277868158277031405)
                  ·
                    refine ⟨2429919854200559353886777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6479786277868158277031405 2429919854200559353886777)
                    ·
                      refine ⟨1822439890650419515415083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2429919854200559353886777 1822439890650419515415083)
                      ·
                        rfl

theorem cell23_3549189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 3, 3, 2].length) (baseStart_3549189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3549189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3549189 prefixEnd_3549189 := by exact prefixLift 3549189
  have htrace : WordTrace (prefixWord ++ tailWord_3549189) baseStart_3549189 baseEnd_3549189 := by
    simpa [prefixWord, tailWord_3549189, baseEnd_3549189] using wordTrace_append hprefix tailTrace_3549189
  have hstable : (prefixWord ++ tailWord_3549189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549189).length < 2 ^ (prefixWord ++ tailWord_3549189).sum := by decide
  have hdescent : baseEnd_3549189 < baseStart_3549189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549232 : List Nat := [2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 4]
def baseStart_3549232 : Nat := 118140960795 + 3549232 * 2 ^ 59
def prefixEnd_3549232 : Nat := 4983230072969 + 3 ^ 40 * 3549232 * 2
def baseEnd_3549232 : Nat := 1822461970318562847177385

theorem tailTrace_3549232 : CollatzResearch.WordTrace tailWord_3549232 prefixEnd_3549232 1822461970318562847177385 := by
  unfold tailWord_3549232
  simp only [CollatzResearch.WordTrace]
  refine ⟨64725562938873049705900975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86300750585164066274534633 64725562938873049705900975)
  ·
    refine ⟨97088344408309574558851463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64725562938873049705900975 97088344408309574558851463)
    ·
      refine ⟨145632516612464361838277195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97088344408309574558851463 145632516612464361838277195)
      ·
        refine ⟨218448774918696542757415793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145632516612464361838277195 218448774918696542757415793)
        ·
          refine ⟨163836581189022407068061845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218448774918696542757415793 163836581189022407068061845)
          ·
            refine ⟨7679839743235425331315399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 163836581189022407068061845 7679839743235425331315399)
            ·
              refine ⟨11519759614853137996973099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7679839743235425331315399 11519759614853137996973099)
              ·
                refine ⟨17279639422279706995459649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11519759614853137996973099 17279639422279706995459649)
                ·
                  refine ⟨12959729566709780246594737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17279639422279706995459649 12959729566709780246594737)
                  ·
                    refine ⟨9719797175032335184946053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12959729566709780246594737 9719797175032335184946053)
                    ·
                      refine ⟨1822461970318562847177385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9719797175032335184946053 1822461970318562847177385)
                      ·
                        rfl

theorem cell23_3549232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 4].length) (baseStart_3549232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3549232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3549232 prefixEnd_3549232 := by exact prefixLift 3549232
  have htrace : WordTrace (prefixWord ++ tailWord_3549232) baseStart_3549232 baseEnd_3549232 := by
    simpa [prefixWord, tailWord_3549232, baseEnd_3549232] using wordTrace_append hprefix tailTrace_3549232
  have hstable : (prefixWord ++ tailWord_3549232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549232).length < 2 ^ (prefixWord ++ tailWord_3549232).sum := by decide
  have hdescent : baseEnd_3549232 < baseStart_3549232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549270 : List Nat := [5, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2]
def baseStart_3549270 : Nat := 118140960795 + 3549270 * 2 ^ 59
def prefixEnd_3549270 : Nat := 4983230072969 + 3 ^ 40 * 3549270 * 2
def baseEnd_3549270 : Nat := 1822481482583433698502211

theorem tailTrace_3549270 : CollatzResearch.WordTrace tailWord_3549270 prefixEnd_3549270 1822481482583433698502211 := by
  unfold tailWord_3549270
  simp only [CollatzResearch.WordTrace]
  refine ⟨8090781990725526993855329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86301674567738954601123509 8090781990725526993855329)
  ·
    refine ⟨6068086493044145245391497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8090781990725526993855329 6068086493044145245391497)
    ·
      refine ⟨4551064869783108934043623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6068086493044145245391497 4551064869783108934043623)
      ·
        refine ⟨6826597304674663401065435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4551064869783108934043623 6826597304674663401065435)
        ·
          refine ⟨10239895957011995101598153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6826597304674663401065435 10239895957011995101598153)
          ·
            refine ⟨7679921967758996326198615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10239895957011995101598153 7679921967758996326198615)
            ·
              refine ⟨11519882951638494489297923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7679921967758996326198615 11519882951638494489297923)
              ·
                refine ⟨17279824427457741733946885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11519882951638494489297923 17279824427457741733946885)
                ·
                  refine ⟨3239967080148326575115041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17279824427457741733946885 3239967080148326575115041)
                  ·
                    refine ⟨2429975310111244931336281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3239967080148326575115041 2429975310111244931336281)
                    ·
                      refine ⟨1822481482583433698502211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2429975310111244931336281 1822481482583433698502211)
                      ·
                        rfl

theorem cell23_3549270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_3549270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3549270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3549270 prefixEnd_3549270 := by exact prefixLift 3549270
  have htrace : WordTrace (prefixWord ++ tailWord_3549270) baseStart_3549270 baseEnd_3549270 := by
    simpa [prefixWord, tailWord_3549270, baseEnd_3549270] using wordTrace_append hprefix tailTrace_3549270
  have hstable : (prefixWord ++ tailWord_3549270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549270).length < 2 ^ (prefixWord ++ tailWord_3549270).sum := by decide
  have hdescent : baseEnd_3549270 < baseStart_3549270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549292 : List Nat := [2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 4]
def baseStart_3549292 : Nat := 118140960795 + 3549292 * 2 ^ 59
def prefixEnd_3549292 : Nat := 4983230072969 + 3 ^ 40 * 3549292 * 2
def baseEnd_3549292 : Nat := 1822492779157832612427109

theorem tailTrace_3549292 : CollatzResearch.WordTrace tailWord_3549292 prefixEnd_3549292 1822492779157832612427109 := by
  unfold tailWord_3549292
  simp only [CollatzResearch.WordTrace]
  refine ⟨64726657128764364829493065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86302209505019153105990753 64726657128764364829493065)
  ·
    refine ⟨48544992846573273622119799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64726657128764364829493065 48544992846573273622119799)
    ·
      refine ⟨72817489269859910433179699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48544992846573273622119799 72817489269859910433179699)
      ·
        refine ⟨109226233904789865649769549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72817489269859910433179699 109226233904789865649769549)
        ·
          refine ⟨40959837714296199618663581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109226233904789865649769549 40959837714296199618663581)
          ·
            refine ⟨15359939142861074856998843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40959837714296199618663581 15359939142861074856998843)
            ·
              refine ⟨23039908714291612285498265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15359939142861074856998843 23039908714291612285498265)
              ·
                refine ⟨17279931535718709214123699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23039908714291612285498265 17279931535718709214123699)
                ·
                  refine ⟨25919897303578063821185549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17279931535718709214123699 25919897303578063821185549)
                  ·
                    refine ⟨9719961488841773932944581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25919897303578063821185549 9719961488841773932944581)
                    ·
                      refine ⟨1822492779157832612427109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9719961488841773932944581 1822492779157832612427109)
                      ·
                        rfl

theorem cell23_3549292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 4].length) (baseStart_3549292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3549292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3549292 prefixEnd_3549292 := by exact prefixLift 3549292
  have htrace : WordTrace (prefixWord ++ tailWord_3549292) baseStart_3549292 baseEnd_3549292 := by
    simpa [prefixWord, tailWord_3549292, baseEnd_3549292] using wordTrace_append hprefix tailTrace_3549292
  have hstable : (prefixWord ++ tailWord_3549292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549292).length < 2 ^ (prefixWord ++ tailWord_3549292).sum := by decide
  have hdescent : baseEnd_3549292 < baseStart_3549292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549326 : List Nat := [4, 1, 1, 3, 3, 1, 1, 2, 2, 1, 4]
def baseStart_3549326 : Nat := 118140960795 + 3549326 * 2 ^ 59
def prefixEnd_3549326 : Nat := 4983230072969 + 3 ^ 40 * 3549326 * 2
def baseEnd_3549326 : Nat := 1822510237500085479401953

theorem tailTrace_3549326 : CollatzResearch.WordTrace tailWord_3549326 prefixEnd_3549326 1822510237500085479401953 := by
  unfold tailWord_3549326
  simp only [CollatzResearch.WordTrace]
  refine ⟨16181819292425694183215479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86303036226270368977149221 16181819292425694183215479)
  ·
    refine ⟨24272728938638541274823219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16181819292425694183215479 24272728938638541274823219)
    ·
      refine ⟨36409093407957811912234829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24272728938638541274823219 36409093407957811912234829)
      ·
        refine ⟨13653410027984179467088061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36409093407957811912234829 13653410027984179467088061)
        ·
          refine ⟨5120028760494067300158023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13653410027984179467088061 5120028760494067300158023)
          ·
            refine ⟨7680043140741100950237035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5120028760494067300158023 7680043140741100950237035)
            ·
              refine ⟨11520064711111651425355553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7680043140741100950237035 11520064711111651425355553)
              ·
                refine ⟨8640048533333738569016665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11520064711111651425355553 8640048533333738569016665)
                ·
                  refine ⟨6480036400000303926762499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8640048533333738569016665 6480036400000303926762499)
                  ·
                    refine ⟨9720054600000455890143749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6480036400000303926762499 9720054600000455890143749)
                    ·
                      refine ⟨1822510237500085479401953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9720054600000455890143749 1822510237500085479401953)
                      ·
                        rfl

theorem cell23_3549326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_3549326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3549326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3549326 prefixEnd_3549326 := by exact prefixLift 3549326
  have htrace : WordTrace (prefixWord ++ tailWord_3549326) baseStart_3549326 baseEnd_3549326 := by
    simpa [prefixWord, tailWord_3549326, baseEnd_3549326] using wordTrace_append hprefix tailTrace_3549326
  have hstable : (prefixWord ++ tailWord_3549326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549326).length < 2 ^ (prefixWord ++ tailWord_3549326).sum := by decide
  have hdescent : baseEnd_3549326 < baseStart_3549326 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549359 : List Nat := [1, 1, 2, 1, 2, 3, 1, 3, 5, 1, 3]
def baseStart_3549359 : Nat := 118140960795 + 3549359 * 2 ^ 59
def prefixEnd_3549359 : Nat := 4983230072969 + 3 ^ 40 * 3549359 * 2
def baseEnd_3549359 : Nat := 1822527182361683850289301

theorem tailTrace_3549359 : CollatzResearch.WordTrace tailWord_3549359 prefixEnd_3549359 1822527182361683850289301 := by
  unfold tailWord_3549359
  simp only [CollatzResearch.WordTrace]
  refine ⟨129455757948286000101675131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86303838632190666734450087 129455757948286000101675131)
  ·
    refine ⟨194183636922429000152512697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129455757948286000101675131 194183636922429000152512697)
    ·
      refine ⟨145637727691821750114384523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194183636922429000152512697 145637727691821750114384523)
      ·
        refine ⟨218456591537732625171576785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145637727691821750114384523 218456591537732625171576785)
        ·
          refine ⟨163842443653299468878682589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218456591537732625171576785 163842443653299468878682589)
          ·
            refine ⟨61440916369987300829505971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163842443653299468878682589 61440916369987300829505971)
            ·
              refine ⟨92161374554980951244258957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61440916369987300829505971 92161374554980951244258957)
              ·
                refine ⟨34560515458117856716597109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92161374554980951244258957 34560515458117856716597109)
                ·
                  refine ⟨3240048324198549067180979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34560515458117856716597109 3240048324198549067180979)
                  ·
                    refine ⟨4860072486297823600771469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3240048324198549067180979 4860072486297823600771469)
                    ·
                      refine ⟨1822527182361683850289301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4860072486297823600771469 1822527182361683850289301)
                      ·
                        rfl

theorem cell23_3549359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 5, 1, 3].length) (baseStart_3549359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3549359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3549359 prefixEnd_3549359 := by exact prefixLift 3549359
  have htrace : WordTrace (prefixWord ++ tailWord_3549359) baseStart_3549359 baseEnd_3549359 := by
    simpa [prefixWord, tailWord_3549359, baseEnd_3549359] using wordTrace_append hprefix tailTrace_3549359
  have hstable : (prefixWord ++ tailWord_3549359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549359).length < 2 ^ (prefixWord ++ tailWord_3549359).sum := by decide
  have hdescent : baseEnd_3549359 < baseStart_3549359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549386 : List Nat := [3, 1, 2, 1, 3, 1, 1, 4, 2, 3, 2]
def baseStart_3549386 : Nat := 118140960795 + 3549386 * 2 ^ 59
def prefixEnd_3549386 : Nat := 4983230072969 + 3 ^ 40 * 3549386 * 2
def baseEnd_3549386 : Nat := 1822541046339355244651677

theorem tailTrace_3549386 : CollatzResearch.WordTrace tailWord_3549386 prefixEnd_3549386 1822541046339355244651677 := by
  unfold tailWord_3549386
  simp only [CollatzResearch.WordTrace]
  refine ⟨32364185679797045928227003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86304495146125455808605341 32364185679797045928227003)
  ·
    refine ⟨48546278519695568892340505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32364185679797045928227003 48546278519695568892340505)
    ·
      refine ⟨36409708889771676669255379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48546278519695568892340505 36409708889771676669255379)
      ·
        refine ⟨54614563334657515003883069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36409708889771676669255379 54614563334657515003883069)
        ·
          refine ⟨20480461250496568126456151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54614563334657515003883069 20480461250496568126456151)
          ·
            refine ⟨30720691875744852189684227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20480461250496568126456151 30720691875744852189684227)
            ·
              refine ⟨46081037813617278284526341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30720691875744852189684227 46081037813617278284526341)
              ·
                refine ⟨8640194590053239678348689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46081037813617278284526341 8640194590053239678348689)
                ·
                  refine ⟨6480145942539929758761517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8640194590053239678348689 6480145942539929758761517)
                  ·
                    refine ⟨2430054728452473659535569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6480145942539929758761517 2430054728452473659535569)
                    ·
                      refine ⟨1822541046339355244651677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2430054728452473659535569 1822541046339355244651677)
                      ·
                        rfl

theorem cell23_3549386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 4, 2, 3, 2].length) (baseStart_3549386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3549386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3549386 prefixEnd_3549386 := by exact prefixLift 3549386
  have htrace : WordTrace (prefixWord ++ tailWord_3549386) baseStart_3549386 baseEnd_3549386 := by
    simpa [prefixWord, tailWord_3549386, baseEnd_3549386] using wordTrace_append hprefix tailTrace_3549386
  have hstable : (prefixWord ++ tailWord_3549386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549386).length < 2 ^ (prefixWord ++ tailWord_3549386).sum := by decide
  have hdescent : baseEnd_3549386 < baseStart_3549386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549399 : List Nat := [1, 1, 3, 2, 1, 2, 1, 2, 2, 6, 2]
def baseStart_3549399 : Nat := 118140960795 + 3549399 * 2 ^ 59
def prefixEnd_3549399 : Nat := 4983230072969 + 3 ^ 40 * 3549399 * 2
def baseEnd_3549399 : Nat := 1822547721587863693789117

theorem tailTrace_3549399 : CollatzResearch.WordTrace tailWord_3549399 prefixEnd_3549399 1822547721587863693789117 := by
  unfold tailWord_3549399
  simp only [CollatzResearch.WordTrace]
  refine ⟨129457216868141086933131251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86304811245427391288754167 129457216868141086933131251)
  ·
    refine ⟨194185825302211630399696877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129457216868141086933131251 194185825302211630399696877)
    ·
      refine ⟨72819684488329361399886329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194185825302211630399696877 72819684488329361399886329)
      ·
        refine ⟨54614763366247021049914747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72819684488329361399886329 54614763366247021049914747)
        ·
          refine ⟨81922145049370531574872121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54614763366247021049914747 81922145049370531574872121)
          ·
            refine ⟨61441608787027898681154091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81922145049370531574872121 61441608787027898681154091)
            ·
              refine ⟨92162413180541848021731137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61441608787027898681154091 92162413180541848021731137)
              ·
                refine ⟨69121809885406386016298353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92162413180541848021731137 69121809885406386016298353)
                ·
                  refine ⟨51841357414054789512223765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69121809885406386016298353 51841357414054789512223765)
                  ·
                    refine ⟨2430063628783818258385489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 51841357414054789512223765 2430063628783818258385489)
                    ·
                      refine ⟨1822547721587863693789117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2430063628783818258385489 1822547721587863693789117)
                      ·
                        rfl

theorem cell23_3549399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 6, 2].length) (baseStart_3549399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3549399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3549399 prefixEnd_3549399 := by exact prefixLift 3549399
  have htrace : WordTrace (prefixWord ++ tailWord_3549399) baseStart_3549399 baseEnd_3549399 := by
    simpa [prefixWord, tailWord_3549399, baseEnd_3549399] using wordTrace_append hprefix tailTrace_3549399
  have hstable : (prefixWord ++ tailWord_3549399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549399).length < 2 ^ (prefixWord ++ tailWord_3549399).sum := by decide
  have hdescent : baseEnd_3549399 < baseStart_3549399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549409 : List Nat := [1, 2, 3, 1, 3, 1, 4, 1, 1, 6]
def baseStart_3549409 : Nat := 118140960795 + 3549409 * 2 ^ 59
def prefixEnd_3549409 : Nat := 4983230072969 + 3 ^ 40 * 3549409 * 2
def baseEnd_3549409 : Nat := 607517618798136218221357

theorem tailTrace_3549409 : CollatzResearch.WordTrace tailWord_3549409 prefixEnd_3549409 607517618798136218221357 := by
  unfold tailWord_3549409
  simp only [CollatzResearch.WordTrace]
  refine ⟨129457581598104858640995281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86305054398736572427330187 129457581598104858640995281)
  ·
    refine ⟨97093186198578643980746461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129457581598104858640995281 97093186198578643980746461)
    ·
      refine ⟨36409944824466991492779923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97093186198578643980746461 36409944824466991492779923)
      ·
        refine ⟨54614917236700487239169885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36409944824466991492779923 54614917236700487239169885)
        ·
          refine ⟨20480593963762682714688707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54614917236700487239169885 20480593963762682714688707)
          ·
            refine ⟨30720890945644024072033061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20480593963762682714688707 30720890945644024072033061)
            ·
              refine ⟨5760167052308254513506199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30720890945644024072033061 5760167052308254513506199)
              ·
                refine ⟨8640250578462381770259299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5760167052308254513506199 8640250578462381770259299)
                ·
                  refine ⟨12960375867693572655388949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8640250578462381770259299 12960375867693572655388949)
                  ·
                    refine ⟨607517618798136218221357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12960375867693572655388949 607517618798136218221357)
                    ·
                      rfl

theorem cell23_3549409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 1, 1, 6].length) (baseStart_3549409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3549409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3549409 prefixEnd_3549409 := by exact prefixLift 3549409
  have htrace : WordTrace (prefixWord ++ tailWord_3549409) baseStart_3549409 baseEnd_3549409 := by
    simpa [prefixWord, tailWord_3549409, baseEnd_3549409] using wordTrace_append hprefix tailTrace_3549409
  have hstable : (prefixWord ++ tailWord_3549409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549409).length < 2 ^ (prefixWord ++ tailWord_3549409).sum := by decide
  have hdescent : baseEnd_3549409 < baseStart_3549409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549419 : List Nat := [1, 1, 1, 1, 2, 5, 1, 3, 3, 2, 3]
def baseStart_3549419 : Nat := 118140960795 + 3549419 * 2 ^ 59
def prefixEnd_3549419 : Nat := 4983230072969 + 3 ^ 40 * 3549419 * 2
def baseEnd_3549419 : Nat := 1822557991200953615539025

theorem tailTrace_3549419 : CollatzResearch.WordTrace tailWord_3549419 prefixEnd_3549419 1822557991200953615539025 := by
  unfold tailWord_3549419
  simp only [CollatzResearch.WordTrace]
  refine ⟨129457946328068630348859311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86305297552045753565906207 129457946328068630348859311)
  ·
    refine ⟨194186919492102945523288967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129457946328068630348859311 194186919492102945523288967)
    ·
      refine ⟨291280379238154418284933451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194186919492102945523288967 291280379238154418284933451)
      ·
        refine ⟨436920568857231627427400177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291280379238154418284933451 436920568857231627427400177)
        ·
          refine ⟨327690426642923720570550133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 436920568857231627427400177 327690426642923720570550133)
          ·
            refine ⟨30720977497774098803489075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 327690426642923720570550133 30720977497774098803489075)
            ·
              refine ⟨46081466246661148205233613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30720977497774098803489075 46081466246661148205233613)
              ·
                refine ⟨17280549842497930576962605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46081466246661148205233613 17280549842497930576962605)
                ·
                  refine ⟨6480206190936723966360977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17280549842497930576962605 6480206190936723966360977)
                  ·
                    refine ⟨4860154643202542974770733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6480206190936723966360977 4860154643202542974770733)
                    ·
                      refine ⟨1822557991200953615539025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4860154643202542974770733 1822557991200953615539025)
                      ·
                        rfl

theorem cell23_3549419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 3, 2, 3].length) (baseStart_3549419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3549419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3549419 prefixEnd_3549419 := by exact prefixLift 3549419
  have htrace : WordTrace (prefixWord ++ tailWord_3549419) baseStart_3549419 baseEnd_3549419 := by
    simpa [prefixWord, tailWord_3549419, baseEnd_3549419] using wordTrace_append hprefix tailTrace_3549419
  have hstable : (prefixWord ++ tailWord_3549419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549419).length < 2 ^ (prefixWord ++ tailWord_3549419).sum := by decide
  have hdescent : baseEnd_3549419 < baseStart_3549419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549450 : List Nat := [3, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2]
def baseStart_3549450 : Nat := 118140960795 + 3549450 * 2 ^ 59
def prefixEnd_3549450 : Nat := 4983230072969 + 3 ^ 40 * 3549450 * 2
def baseEnd_3549450 : Nat := 1822573909101242994251383

theorem tailTrace_3549450 : CollatzResearch.WordTrace tailWord_3549450 prefixEnd_3549450 1822573909101242994251383 := by
  unfold tailWord_3549450
  simp only [CollatzResearch.WordTrace]
  refine ⟨32364769247739080660809451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86306051327304215095491869 32364769247739080660809451)
  ·
    refine ⟨48547153871608620991214177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32364769247739080660809451 48547153871608620991214177)
    ·
      refine ⟨36410365403706465743410633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48547153871608620991214177 36410365403706465743410633)
      ·
        refine ⟨27307774052779849307557975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36410365403706465743410633 27307774052779849307557975)
        ·
          refine ⟨40961661079169773961336963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27307774052779849307557975 40961661079169773961336963)
          ·
            refine ⟨61442491618754660942005445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40961661079169773961336963 61442491618754660942005445)
            ·
              refine ⟨11520467178516498926626021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61442491618754660942005445 11520467178516498926626021)
              ·
                refine ⟨2160087595971843548742379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11520467178516498926626021 2160087595971843548742379)
                ·
                  refine ⟨3240131393957765323113569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2160087595971843548742379 3240131393957765323113569)
                  ·
                    refine ⟨2430098545468323992335177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3240131393957765323113569 2430098545468323992335177)
                    ·
                      refine ⟨1822573909101242994251383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2430098545468323992335177 1822573909101242994251383)
                      ·
                        rfl

theorem cell23_3549450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2].length) (baseStart_3549450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3549450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3549450 prefixEnd_3549450 := by exact prefixLift 3549450
  have htrace : WordTrace (prefixWord ++ tailWord_3549450) baseStart_3549450 baseEnd_3549450 := by
    simpa [prefixWord, tailWord_3549450, baseEnd_3549450] using wordTrace_append hprefix tailTrace_3549450
  have hstable : (prefixWord ++ tailWord_3549450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549450).length < 2 ^ (prefixWord ++ tailWord_3549450).sum := by decide
  have hdescent : baseEnd_3549450 < baseStart_3549450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549470 : List Nat := [4, 3, 2, 1, 1, 1, 1, 4, 1, 2, 3]
def baseStart_3549470 : Nat := 118140960795 + 3549470 * 2 ^ 59
def prefixEnd_3549470 : Nat := 4983230072969 + 3 ^ 40 * 3549470 * 2
def baseEnd_3549470 : Nat := 1822584178714332916001291

theorem tailTrace_3549470 : CollatzResearch.WordTrace tailWord_3549470 prefixEnd_3549470 1822584178714332916001291 := by
  unfold tailWord_3549470
  simp only [CollatzResearch.WordTrace]
  refine ⟨16182475806360483257370733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86306537633922577372643909 16182475806360483257370733)
  ·
    refine ⟨6068428427385181221514025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16182475806360483257370733 6068428427385181221514025)
    ·
      refine ⟨4551321320538885916135519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6068428427385181221514025 4551321320538885916135519)
      ·
        refine ⟨6826981980808328874203279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4551321320538885916135519 6826981980808328874203279)
        ·
          refine ⟨10240472971212493311304919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6826981980808328874203279 10240472971212493311304919)
          ·
            refine ⟨15360709456818739966957379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10240472971212493311304919 15360709456818739966957379)
            ·
              refine ⟨23041064185228109950436069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15360709456818739966957379 23041064185228109950436069)
              ·
                refine ⟨4320199534730270615706763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23041064185228109950436069 4320199534730270615706763)
                ·
                  refine ⟨6480299302095405923560145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4320199534730270615706763 6480299302095405923560145)
                  ·
                    refine ⟨4860224476571554442670109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6480299302095405923560145 4860224476571554442670109)
                    ·
                      refine ⟨1822584178714332916001291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4860224476571554442670109 1822584178714332916001291)
                      ·
                        rfl

theorem cell23_3549470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_3549470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3549470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3549470 prefixEnd_3549470 := by exact prefixLift 3549470
  have htrace : WordTrace (prefixWord ++ tailWord_3549470) baseStart_3549470 baseEnd_3549470 := by
    simpa [prefixWord, tailWord_3549470, baseEnd_3549470] using wordTrace_append hprefix tailTrace_3549470
  have hstable : (prefixWord ++ tailWord_3549470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549470).length < 2 ^ (prefixWord ++ tailWord_3549470).sum := by decide
  have hdescent : baseEnd_3549470 < baseStart_3549470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549493 : List Nat := [1, 3, 3, 1, 2, 1, 1, 5, 1, 3, 2]
def baseStart_3549493 : Nat := 118140960795 + 3549493 * 2 ^ 59
def prefixEnd_3549493 : Nat := 4983230072969 + 3 ^ 40 * 3549493 * 2
def baseEnd_3549493 : Nat := 1822595988769386326013685

theorem tailTrace_3549493 : CollatzResearch.WordTrace tailWord_3549493 prefixEnd_3549493 1822595988769386326013685 := by
  unfold tailWord_3549493
  simp only [CollatzResearch.WordTrace]
  refine ⟨129460645329800540987053133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86307096886533693991368755 129460645329800540987053133)
  ·
    refine ⟨48547741998675202870144925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129460645329800540987053133 48547741998675202870144925)
    ·
      refine ⟨18205403249503201076304347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48547741998675202870144925 18205403249503201076304347)
      ·
        refine ⟨27308104874254801614456521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18205403249503201076304347 27308104874254801614456521)
        ·
          refine ⟨20481078655691101210842391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27308104874254801614456521 20481078655691101210842391)
          ·
            refine ⟨30721617983536651816263587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20481078655691101210842391 30721617983536651816263587)
            ·
              refine ⟨46082426975304977724395381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30721617983536651816263587 46082426975304977724395381)
              ·
                refine ⟨4320227528934841661662067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46082426975304977724395381 4320227528934841661662067)
                ·
                  refine ⟨6480341293402262492493101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4320227528934841661662067 6480341293402262492493101)
                  ·
                    refine ⟨2430127985025848434684913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6480341293402262492493101 2430127985025848434684913)
                    ·
                      refine ⟨1822595988769386326013685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2430127985025848434684913 1822595988769386326013685)
                      ·
                        rfl

theorem cell23_3549493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 5, 1, 3, 2].length) (baseStart_3549493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3549493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3549493 prefixEnd_3549493 := by exact prefixLift 3549493
  have htrace : WordTrace (prefixWord ++ tailWord_3549493) baseStart_3549493 baseEnd_3549493 := by
    simpa [prefixWord, tailWord_3549493, baseEnd_3549493] using wordTrace_append hprefix tailTrace_3549493
  have hstable : (prefixWord ++ tailWord_3549493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549493).length < 2 ^ (prefixWord ++ tailWord_3549493).sum := by decide
  have hdescent : baseEnd_3549493 < baseStart_3549493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549534 : List Nat := [4, 4, 2, 1, 1, 1, 1, 2, 1, 3, 3]
def baseStart_3549534 : Nat := 118140960795 + 3549534 * 2 ^ 59
def prefixEnd_3549534 : Nat := 4983230072969 + 3 ^ 40 * 3549534 * 2
def baseEnd_3549534 : Nat := 1822617041476220665600997

theorem tailTrace_3549534 : CollatzResearch.WordTrace tailWord_3549534 prefixEnd_3549534 1822617041476220665600997 := by
  unfold tailWord_3549534
  simp only [CollatzResearch.WordTrace]
  refine ⟨16182767590331500623661957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86308093815101336659530437 16182767590331500623661957)
  ·
    refine ⟨3034268923187156366936617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16182767590331500623661957 3034268923187156366936617)
    ·
      refine ⟨2275701692390367275202463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3034268923187156366936617 2275701692390367275202463)
      ·
        refine ⟨3413552538585550912803695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2275701692390367275202463 3413552538585550912803695)
        ·
          refine ⟨5120328807878326369205543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3413552538585550912803695 5120328807878326369205543)
          ·
            refine ⟨7680493211817489553808315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5120328807878326369205543 7680493211817489553808315)
            ·
              refine ⟨11520739817726234330712473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7680493211817489553808315 11520739817726234330712473)
              ·
                refine ⟨8640554863294675748034355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11520739817726234330712473 8640554863294675748034355)
                ·
                  refine ⟨12960832294942013622051533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8640554863294675748034355 12960832294942013622051533)
                  ·
                    refine ⟨4860312110603255108269325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12960832294942013622051533 4860312110603255108269325)
                    ·
                      refine ⟨1822617041476220665600997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4860312110603255108269325 1822617041476220665600997)
                      ·
                        rfl

theorem cell23_3549534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_3549534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3549534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3549534 prefixEnd_3549534 := by exact prefixLift 3549534
  have htrace : WordTrace (prefixWord ++ tailWord_3549534) baseStart_3549534 baseEnd_3549534 := by
    simpa [prefixWord, tailWord_3549534, baseEnd_3549534] using wordTrace_append hprefix tailTrace_3549534
  have hstable : (prefixWord ++ tailWord_3549534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549534).length < 2 ^ (prefixWord ++ tailWord_3549534).sum := by decide
  have hdescent : baseEnd_3549534 < baseStart_3549534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549557 : List Nat := [1, 3, 4, 1, 2, 2, 2, 2, 2, 2, 2]
def baseStart_3549557 : Nat := 118140960795 + 3549557 * 2 ^ 59
def prefixEnd_3549557 : Nat := 4983230072969 + 3 ^ 40 * 3549557 * 2
def baseEnd_3549557 : Nat := 1822628851531274075613391

theorem tailTrace_3549557 : CollatzResearch.WordTrace tailWord_3549557 prefixEnd_3549557 1822628851531274075613391 := by
  unfold tailWord_3549557
  simp only [CollatzResearch.WordTrace]
  refine ⟨129462979601568679917382925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86308653067712453278255283 129462979601568679917382925)
  ·
    refine ⟨48548617350588254969018597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129462979601568679917382925 48548617350588254969018597)
    ·
      refine ⟨9102865753235297806690987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48548617350588254969018597 9102865753235297806690987)
      ·
        refine ⟨13654298629852946710036481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9102865753235297806690987 13654298629852946710036481)
        ·
          refine ⟨10240723972389710032527361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13654298629852946710036481 10240723972389710032527361)
          ·
            refine ⟨7680542979292282524395521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10240723972389710032527361 7680542979292282524395521)
            ·
              refine ⟨5760407234469211893296641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7680542979292282524395521 5760407234469211893296641)
              ·
                refine ⟨4320305425851908919972481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5760407234469211893296641 4320305425851908919972481)
                ·
                  refine ⟨3240229069388931689979361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4320305425851908919972481 3240229069388931689979361)
                  ·
                    refine ⟨2430171802041698767484521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3240229069388931689979361 2430171802041698767484521)
                    ·
                      refine ⟨1822628851531274075613391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2430171802041698767484521 1822628851531274075613391)
                      ·
                        rfl

theorem cell23_3549557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_3549557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3549557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3549557 prefixEnd_3549557 := by exact prefixLift 3549557
  have htrace : WordTrace (prefixWord ++ tailWord_3549557) baseStart_3549557 baseEnd_3549557 := by
    simpa [prefixWord, tailWord_3549557, baseEnd_3549557] using wordTrace_append hprefix tailTrace_3549557
  have hstable : (prefixWord ++ tailWord_3549557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549557).length < 2 ^ (prefixWord ++ tailWord_3549557).sum := by decide
  have hdescent : baseEnd_3549557 < baseStart_3549557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549559 : List Nat := [1, 1, 3, 1, 1, 2, 2, 3, 4, 5]
def baseStart_3549559 : Nat := 118140960795 + 3549559 * 2 ^ 59
def prefixEnd_3549559 : Nat := 4983230072969 + 3 ^ 40 * 3549559 * 2
def baseEnd_3549559 : Nat := 607543292830861022596127

theorem tailTrace_3549559 : CollatzResearch.WordTrace tailWord_3549559 prefixEnd_3549559 607543292830861022596127 := by
  unfold tailWord_3549559
  simp only [CollatzResearch.WordTrace]
  refine ⟨129463052547561434258955731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86308701698374289505970487 129463052547561434258955731)
  ·
    refine ⟨194194578821342151388433597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129463052547561434258955731 194194578821342151388433597)
    ·
      refine ⟨72822967058003306770662599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194194578821342151388433597 72822967058003306770662599)
      ·
        refine ⟨109234450587004960155993899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72822967058003306770662599 109234450587004960155993899)
        ·
          refine ⟨163851675880507440233990849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109234450587004960155993899 163851675880507440233990849)
          ·
            refine ⟨122888756910380580175493137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163851675880507440233990849 122888756910380580175493137)
            ·
              refine ⟨92166567682785435131619853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122888756910380580175493137 92166567682785435131619853)
              ·
                refine ⟨34562462881044538174357445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92166567682785435131619853 34562462881044538174357445)
                ·
                  refine ⟨6480461790195850907692021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34562462881044538174357445 6480461790195850907692021)
                  ·
                    refine ⟨607543292830861022596127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6480461790195850907692021 607543292830861022596127)
                    ·
                      rfl

theorem cell23_3549559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 4, 5].length) (baseStart_3549559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3549559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3549559 prefixEnd_3549559 := by exact prefixLift 3549559
  have htrace : WordTrace (prefixWord ++ tailWord_3549559) baseStart_3549559 baseEnd_3549559 := by
    simpa [prefixWord, tailWord_3549559, baseEnd_3549559] using wordTrace_append hprefix tailTrace_3549559
  have hstable : (prefixWord ++ tailWord_3549559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549559).length < 2 ^ (prefixWord ++ tailWord_3549559).sum := by decide
  have hdescent : baseEnd_3549559 < baseStart_3549559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549563 : List Nat := [1, 1, 1, 1, 1, 7, 4, 2, 5]
def baseStart_3549563 : Nat := 118140960795 + 3549563 * 2 ^ 59
def prefixEnd_3549563 : Nat := 4983230072969 + 3 ^ 40 * 3549563 * 2
def baseEnd_3549563 : Nat := 202514659157244561348707

theorem tailTrace_3549563 : CollatzResearch.WordTrace tailWord_3549563 prefixEnd_3549563 202514659157244561348707 := by
  unfold tailWord_3549563
  simp only [CollatzResearch.WordTrace]
  refine ⟨129463198439546942942101343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86308798959697961961400895 129463198439546942942101343)
  ·
    refine ⟨194194797659320414413152015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129463198439546942942101343 194194797659320414413152015)
    ·
      refine ⟨291292196488980621619728023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194194797659320414413152015 291292196488980621619728023)
      ·
        refine ⟨436938294733470932429592035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291292196488980621619728023 436938294733470932429592035)
        ·
          refine ⟨655407442100206398644388053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436938294733470932429592035 655407442100206398644388053)
          ·
            refine ⟨15361111924223587468227845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 655407442100206398644388053 15361111924223587468227845)
            ·
              refine ⟨2880208485791922650292721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15361111924223587468227845 2880208485791922650292721)
              ·
                refine ⟨2160156364343941987719541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2880208485791922650292721 2160156364343941987719541)
                ·
                  refine ⟨202514659157244561348707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2160156364343941987719541 202514659157244561348707)
                  ·
                    rfl

theorem cell23_3549563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4, 2, 5].length) (baseStart_3549563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3549563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3549563 prefixEnd_3549563 := by exact prefixLift 3549563
  have htrace : WordTrace (prefixWord ++ tailWord_3549563) baseStart_3549563 baseEnd_3549563 := by
    simpa [prefixWord, tailWord_3549563, baseEnd_3549563] using wordTrace_append hprefix tailTrace_3549563
  have hstable : (prefixWord ++ tailWord_3549563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549563).length < 2 ^ (prefixWord ++ tailWord_3549563).sum := by decide
  have hdescent : baseEnd_3549563 < baseStart_3549563 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549570 : List Nat := [3, 4, 2, 1, 2, 1, 1, 1, 2, 2, 4]
def baseStart_3549570 : Nat := 118140960795 + 3549570 * 2 ^ 59
def prefixEnd_3549570 : Nat := 4983230072969 + 3 ^ 40 * 3549570 * 2
def baseEnd_3549570 : Nat := 1822635526779782524750831

theorem tailTrace_3549570 : CollatzResearch.WordTrace tailWord_3549570 prefixEnd_3549570 1822635526779782524750831 := by
  unfold tailWord_3549570
  simp only [CollatzResearch.WordTrace]
  refine ⟨32365863437630395784401541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86308969167014388758404109 32365863437630395784401541)
  ·
    refine ⟨6068599394555699209575289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32365863437630395784401541 6068599394555699209575289)
    ·
      refine ⟨4551449545916774407181467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6068599394555699209575289 4551449545916774407181467)
      ·
        refine ⟨6827174318875161610772201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4551449545916774407181467 6827174318875161610772201)
        ·
          refine ⟨5120380739156371208079151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6827174318875161610772201 5120380739156371208079151)
          ·
            refine ⟨7680571108734556812118727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5120380739156371208079151 7680571108734556812118727)
            ·
              refine ⟨11520856663101835218178091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7680571108734556812118727 11520856663101835218178091)
              ·
                refine ⟨17281284994652752827267137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11520856663101835218178091 17281284994652752827267137)
                ·
                  refine ⟨12960963745989564620450353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17281284994652752827267137 12960963745989564620450353)
                  ·
                    refine ⟨9720722809492173465337765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12960963745989564620450353 9720722809492173465337765)
                    ·
                      refine ⟨1822635526779782524750831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9720722809492173465337765 1822635526779782524750831)
                      ·
                        rfl

theorem cell23_3549570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_3549570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3549570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3549570 prefixEnd_3549570 := by exact prefixLift 3549570
  have htrace : WordTrace (prefixWord ++ tailWord_3549570) baseStart_3549570 baseEnd_3549570 := by
    simpa [prefixWord, tailWord_3549570, baseEnd_3549570] using wordTrace_append hprefix tailTrace_3549570
  have hstable : (prefixWord ++ tailWord_3549570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549570).length < 2 ^ (prefixWord ++ tailWord_3549570).sum := by decide
  have hdescent : baseEnd_3549570 < baseStart_3549570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549609 : List Nat := [1, 2, 1, 1, 1, 1, 3, 2, 1, 6, 4]
def baseStart_3549609 : Nat := 118140960795 + 3549609 * 2 ^ 59
def prefixEnd_3549609 : Nat := 4983230072969 + 3 ^ 40 * 3549609 * 2
def baseEnd_3549609 : Nat := 1822655552525307872163151

theorem tailTrace_3549609 : CollatzResearch.WordTrace tailWord_3549609 prefixEnd_3549609 1822655552525307872163151 := by
  unfold tailWord_3549609
  simp only [CollatzResearch.WordTrace]
  refine ⟨129464876197380292798275881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86309917464920195198850587 129464876197380292798275881)
  ·
    refine ⟨97098657148035219598706911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129464876197380292798275881 97098657148035219598706911)
    ·
      refine ⟨145647985722052829398060367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97098657148035219598706911 145647985722052829398060367)
      ·
        refine ⟨218471978583079244097090551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145647985722052829398060367 218471978583079244097090551)
        ·
          refine ⟨327707967874618866145635827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218471978583079244097090551 327707967874618866145635827)
          ·
            refine ⟨491561951811928299218453741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327707967874618866145635827 491561951811928299218453741)
            ·
              refine ⟨184335731929473112206920153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 491561951811928299218453741 184335731929473112206920153)
              ·
                refine ⟨138251798947104834155190115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184335731929473112206920153 138251798947104834155190115)
                ·
                  refine ⟨207377698420657251232785173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138251798947104834155190115 207377698420657251232785173)
                  ·
                    refine ⟨9720829613468308651536805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 207377698420657251232785173 9720829613468308651536805)
                    ·
                      refine ⟨1822655552525307872163151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9720829613468308651536805 1822655552525307872163151)
                      ·
                        rfl

theorem cell23_3549609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 6, 4].length) (baseStart_3549609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3549609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3549609 prefixEnd_3549609 := by exact prefixLift 3549609
  have htrace : WordTrace (prefixWord ++ tailWord_3549609) baseStart_3549609 baseEnd_3549609 := by
    simpa [prefixWord, tailWord_3549609, baseEnd_3549609] using wordTrace_append hprefix tailTrace_3549609
  have hstable : (prefixWord ++ tailWord_3549609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549609).length < 2 ^ (prefixWord ++ tailWord_3549609).sum := by decide
  have hdescent : baseEnd_3549609 < baseStart_3549609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549623 : List Nat := [1, 1, 3, 1, 3, 4, 2, 1, 3, 4]
def baseStart_3549623 : Nat := 118140960795 + 3549623 * 2 ^ 59
def prefixEnd_3549623 : Nat := 4983230072969 + 3 ^ 40 * 3549623 * 2
def baseEnd_3549623 : Nat := 607554247084823605796029

theorem tailTrace_3549623 : CollatzResearch.WordTrace tailWord_3549623 prefixEnd_3549623 607554247084823605796029 := by
  unfold tailWord_3549623
  simp only [CollatzResearch.WordTrace]
  refine ⟨129465386819329573189285523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86310257879553048792857015 129465386819329573189285523)
  ·
    refine ⟨194198080228994359783928285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129465386819329573189285523 194198080228994359783928285)
    ·
      refine ⟨72824280085872884918973107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194198080228994359783928285 72824280085872884918973107)
      ·
        refine ⟨109236420128809327378459661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72824280085872884918973107 109236420128809327378459661)
        ·
          refine ⟨40963657548303497766922373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109236420128809327378459661 40963657548303497766922373)
          ·
            refine ⟨7680685790306905831297945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40963657548303497766922373 7680685790306905831297945)
            ·
              refine ⟨5760514342730179373473459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7680685790306905831297945 5760514342730179373473459)
              ·
                refine ⟨8640771514095269060210189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5760514342730179373473459 8640771514095269060210189)
                ·
                  refine ⟨3240289317785725897578821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8640771514095269060210189 3240289317785725897578821)
                  ·
                    refine ⟨607554247084823605796029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3240289317785725897578821 607554247084823605796029)
                    ·
                      rfl

theorem cell23_3549623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 3, 4].length) (baseStart_3549623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3549623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3549623 prefixEnd_3549623 := by exact prefixLift 3549623
  have htrace : WordTrace (prefixWord ++ tailWord_3549623) baseStart_3549623 baseEnd_3549623 := by
    simpa [prefixWord, tailWord_3549623, baseEnd_3549623] using wordTrace_append hprefix tailTrace_3549623
  have hstable : (prefixWord ++ tailWord_3549623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549623).length < 2 ^ (prefixWord ++ tailWord_3549623).sum := by decide
  have hdescent : baseEnd_3549623 < baseStart_3549623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549646 : List Nat := [4, 1, 1, 1, 2, 1, 1, 1, 1, 7, 3]
def baseStart_3549646 : Nat := 118140960795 + 3549646 * 2 ^ 59
def prefixEnd_3549646 : Nat := 4983230072969 + 3 ^ 40 * 3549646 * 2
def baseEnd_3549646 : Nat := 1822674551309524227400481

theorem tailTrace_3549646 : CollatzResearch.WordTrace tailWord_3549646 prefixEnd_3549646 1822674551309524227400481 := by
  unfold tailWord_3549646
  simp only [CollatzResearch.WordTrace]
  refine ⟨16183278212280781014671599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86310817132164165411581861 16183278212280781014671599)
  ·
    refine ⟨24274917318421171522007399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16183278212280781014671599 24274917318421171522007399)
    ·
      refine ⟨36412375977631757283011099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24274917318421171522007399 36412375977631757283011099)
      ·
        refine ⟨54618563966447635924516649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36412375977631757283011099 54618563966447635924516649)
        ·
          refine ⟨40963922974835726943387487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54618563966447635924516649 40963922974835726943387487)
          ·
            refine ⟨61445884462253590415081231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40963922974835726943387487 61445884462253590415081231)
            ·
              refine ⟨92168826693380385622621847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61445884462253590415081231 92168826693380385622621847)
              ·
                refine ⟨138253240040070578433932771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92168826693380385622621847 138253240040070578433932771)
                ·
                  refine ⟨207379860060105867650899157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138253240040070578433932771 207379860060105867650899157)
                  ·
                    refine ⟨4860465470158731273067949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 207379860060105867650899157 4860465470158731273067949)
                    ·
                      refine ⟨1822674551309524227400481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4860465470158731273067949 1822674551309524227400481)
                      ·
                        rfl

theorem cell23_3549646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 1, 7, 3].length) (baseStart_3549646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3549646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3549646 prefixEnd_3549646 := by exact prefixLift 3549646
  have htrace : WordTrace (prefixWord ++ tailWord_3549646) baseStart_3549646 baseEnd_3549646 := by
    simpa [prefixWord, tailWord_3549646, baseEnd_3549646] using wordTrace_append hprefix tailTrace_3549646
  have hstable : (prefixWord ++ tailWord_3549646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549646).length < 2 ^ (prefixWord ++ tailWord_3549646).sum := by decide
  have hdescent : baseEnd_3549646 < baseStart_3549646 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549649 : List Nat := [1, 2, 2, 1, 2, 1, 1, 2, 2, 9]
def baseStart_3549649 : Nat := 118140960795 + 3549649 * 2 ^ 59
def prefixEnd_3549649 : Nat := 4983230072969 + 3 ^ 40 * 3549649 * 2
def baseEnd_3549649 : Nat := 607558697250495905220989

theorem tailTrace_3549649 : CollatzResearch.WordTrace tailWord_3549649 prefixEnd_3549649 607558697250495905220989 := by
  unfold tailWord_3549649
  simp only [CollatzResearch.WordTrace]
  refine ⟨129466335117235379629732001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86310890078156919753154667 129466335117235379629732001)
  ·
    refine ⟨97099751337926534722299001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129466335117235379629732001 97099751337926534722299001)
    ·
      refine ⟨72824813503444901041724251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97099751337926534722299001 72824813503444901041724251)
      ·
        refine ⟨109237220255167351562586377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72824813503444901041724251 109237220255167351562586377)
        ·
          refine ⟨81927915191375513671939783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109237220255167351562586377 81927915191375513671939783)
          ·
            refine ⟨122891872787063270507909675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81927915191375513671939783 122891872787063270507909675)
            ·
              refine ⟨184337809180594905761864513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122891872787063270507909675 184337809180594905761864513)
              ·
                refine ⟨138253356885446179321398385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184337809180594905761864513 138253356885446179321398385)
                ·
                  refine ⟨103690017664084634491048789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138253356885446179321398385 103690017664084634491048789)
                  ·
                    refine ⟨607558697250495905220989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 103690017664084634491048789 607558697250495905220989)
                    ·
                      rfl

theorem cell23_3549649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 9].length) (baseStart_3549649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3549649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3549649 prefixEnd_3549649 := by exact prefixLift 3549649
  have htrace : WordTrace (prefixWord ++ tailWord_3549649) baseStart_3549649 baseEnd_3549649 := by
    simpa [prefixWord, tailWord_3549649, baseEnd_3549649] using wordTrace_append hprefix tailTrace_3549649
  have hstable : (prefixWord ++ tailWord_3549649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549649).length < 2 ^ (prefixWord ++ tailWord_3549649).sum := by decide
  have hdescent : baseEnd_3549649 < baseStart_3549649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549700 : List Nat := [2, 3, 2, 3, 1, 1, 3, 2, 1, 5]
def baseStart_3549700 : Nat := 118140960795 + 3549700 * 2 ^ 59
def prefixEnd_3549700 : Nat := 4983230072969 + 3 ^ 40 * 3549700 * 2
def baseEnd_3549700 : Nat := 607567426421622338708411

theorem tailTrace_3549700 : CollatzResearch.WordTrace tailWord_3549700 prefixEnd_3549700 607567426421622338708411 := by
  unfold tailWord_3549700
  simp only [CollatzResearch.WordTrace]
  refine ⟨64734097620025307669919277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86312130160033743559892369 64734097620025307669919277)
  ·
    refine ⟨24275286607509490376219729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64734097620025307669919277 24275286607509490376219729)
    ·
      refine ⟨18206464955632117782164797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24275286607509490376219729 18206464955632117782164797)
      ·
        refine ⟨6827424358362044168311799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18206464955632117782164797 6827424358362044168311799)
        ·
          refine ⟨10241136537543066252467699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6827424358362044168311799 10241136537543066252467699)
          ·
            refine ⟨15361704806314599378701549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10241136537543066252467699 15361704806314599378701549)
            ·
              refine ⟨5760639302367974767013081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15361704806314599378701549 5760639302367974767013081)
              ·
                refine ⟨4320479476775981075259811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5760639302367974767013081 4320479476775981075259811)
                ·
                  refine ⟨6480719215163971612889717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4320479476775981075259811 6480719215163971612889717)
                  ·
                    refine ⟨607567426421622338708411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6480719215163971612889717 607567426421622338708411)
                    ·
                      rfl

theorem cell23_3549700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_3549700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3549700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3549700 prefixEnd_3549700 := by exact prefixLift 3549700
  have htrace : WordTrace (prefixWord ++ tailWord_3549700) baseStart_3549700 baseEnd_3549700 := by
    simpa [prefixWord, tailWord_3549700, baseEnd_3549700] using wordTrace_append hprefix tailTrace_3549700
  have hstable : (prefixWord ++ tailWord_3549700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549700).length < 2 ^ (prefixWord ++ tailWord_3549700).sum := by decide
  have hdescent : baseEnd_3549700 < baseStart_3549700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549746 : List Nat := [3, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6]
def baseStart_3549746 : Nat := 118140960795 + 3549746 * 2 ^ 59
def prefixEnd_3549746 : Nat := 4983230072969 + 3 ^ 40 * 3549746 * 2
def baseEnd_3549746 : Nat := 1822725899374973836150021

theorem tailTrace_3549746 : CollatzResearch.WordTrace tailWord_3549746 prefixEnd_3549746 1822725899374973836150021 := by
  unfold tailWord_3549746
  simp only [CollatzResearch.WordTrace]
  refine ⟨32367468249470991299003273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86313248665255976797342061 32367468249470991299003273)
  ·
    refine ⟨24275601187103243474252455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32367468249470991299003273 24275601187103243474252455)
    ·
      refine ⟨36413401780654865211378683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24275601187103243474252455 36413401780654865211378683)
      ·
        refine ⟨54620102670982297817068025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36413401780654865211378683 54620102670982297817068025)
        ·
          refine ⟨40965077003236723362801019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54620102670982297817068025 40965077003236723362801019)
          ·
            refine ⟨61447615504855085044201529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40965077003236723362801019 61447615504855085044201529)
            ·
              refine ⟨46085711628641313783151147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61447615504855085044201529 46085711628641313783151147)
              ·
                refine ⟨69128567442961970674726721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46085711628641313783151147 69128567442961970674726721)
                ·
                  refine ⟨51846425582221478006045041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69128567442961970674726721 51846425582221478006045041)
                  ·
                    refine ⟨38884819186666108504533781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51846425582221478006045041 38884819186666108504533781)
                    ·
                      refine ⟨1822725899374973836150021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38884819186666108504533781 1822725899374973836150021)
                      ·
                        rfl

theorem cell23_3549746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_3549746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3549746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3549746 prefixEnd_3549746 := by exact prefixLift 3549746
  have htrace : WordTrace (prefixWord ++ tailWord_3549746) baseStart_3549746 baseEnd_3549746 := by
    simpa [prefixWord, tailWord_3549746, baseEnd_3549746] using wordTrace_append hprefix tailTrace_3549746
  have hstable : (prefixWord ++ tailWord_3549746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549746).length < 2 ^ (prefixWord ++ tailWord_3549746).sum := by decide
  have hdescent : baseEnd_3549746 < baseStart_3549746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549750 : List Nat := [5, 1, 2, 1, 2, 1, 1, 3, 1, 2, 4]
def baseStart_3549750 : Nat := 118140960795 + 3549750 * 2 ^ 59
def prefixEnd_3549750 : Nat := 4983230072969 + 3 ^ 40 * 3549750 * 2
def baseEnd_3549750 : Nat := 1822727953297591820500003

theorem tailTrace_3549750 : CollatzResearch.WordTrace tailWord_3549750 prefixEnd_3549750 1822727953297591820500003 := by
  unfold tailWord_3549750
  simp only [CollatzResearch.WordTrace]
  refine ⟨8091876180616842117447419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86313345926579649252772469 8091876180616842117447419)
  ·
    refine ⟨12137814270925263176171129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8091876180616842117447419 12137814270925263176171129)
    ·
      refine ⟨9103360703193947382128347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12137814270925263176171129 9103360703193947382128347)
      ·
        refine ⟨13655041054790921073192521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9103360703193947382128347 13655041054790921073192521)
        ·
          refine ⟨10241280791093190804894391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13655041054790921073192521 10241280791093190804894391)
          ·
            refine ⟨15361921186639786207341587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10241280791093190804894391 15361921186639786207341587)
            ·
              refine ⟨23042881779959679311012381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15361921186639786207341587 23042881779959679311012381)
              ·
                refine ⟨8641080667484879741629643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23042881779959679311012381 8641080667484879741629643)
                ·
                  refine ⟨12961621001227319612444465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8641080667484879741629643 12961621001227319612444465)
                  ·
                    refine ⟨9721215750920489709333349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12961621001227319612444465 9721215750920489709333349)
                    ·
                      refine ⟨1822727953297591820500003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9721215750920489709333349 1822727953297591820500003)
                      ·
                        rfl

theorem cell23_3549750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_3549750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3549750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3549750 prefixEnd_3549750 := by exact prefixLift 3549750
  have htrace : WordTrace (prefixWord ++ tailWord_3549750) baseStart_3549750 baseEnd_3549750 := by
    simpa [prefixWord, tailWord_3549750, baseEnd_3549750] using wordTrace_append hprefix tailTrace_3549750
  have hstable : (prefixWord ++ tailWord_3549750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549750).length < 2 ^ (prefixWord ++ tailWord_3549750).sum := by decide
  have hdescent : baseEnd_3549750 < baseStart_3549750 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549776 : List Nat := [2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 4]
def baseStart_3549776 : Nat := 118140960795 + 3549776 * 2 ^ 59
def prefixEnd_3549776 : Nat := 4983230072969 + 3 ^ 40 * 3549776 * 2
def baseEnd_3549776 : Nat := 1822741303794608718774883

theorem tailTrace_3549776 : CollatzResearch.WordTrace tailWord_3549776 prefixEnd_3549776 1822741303794608718774883 := by
  unfold tailWord_3549776
  simp only [CollatzResearch.WordTrace]
  refine ⟨64735483593887640159802591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86313978125183520213070121 64735483593887640159802591)
  ·
    refine ⟨97103225390831460239703887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64735483593887640159802591 97103225390831460239703887)
    ·
      refine ⟨145654838086247190359555831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97103225390831460239703887 145654838086247190359555831)
      ·
        refine ⟨218482257129370785539333747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145654838086247190359555831 218482257129370785539333747)
        ·
          refine ⟨327723385694056178309000621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218482257129370785539333747 327723385694056178309000621)
          ·
            refine ⟨122896269635271066865875233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 327723385694056178309000621 122896269635271066865875233)
            ·
              refine ⟨92172202226453300149406425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122896269635271066865875233 92172202226453300149406425)
              ·
                refine ⟨69129151669839975112054819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92172202226453300149406425 69129151669839975112054819)
                ·
                  refine ⟨103693727504759962668082229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69129151669839975112054819 103693727504759962668082229)
                  ·
                    refine ⟨9721286953571246500132709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 103693727504759962668082229 9721286953571246500132709)
                    ·
                      refine ⟨1822741303794608718774883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9721286953571246500132709 1822741303794608718774883)
                      ·
                        rfl

theorem cell23_3549776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 4].length) (baseStart_3549776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3549776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3549776 prefixEnd_3549776 := by exact prefixLift 3549776
  have htrace : WordTrace (prefixWord ++ tailWord_3549776) baseStart_3549776 baseEnd_3549776 := by
    simpa [prefixWord, tailWord_3549776, baseEnd_3549776] using wordTrace_append hprefix tailTrace_3549776
  have hstable : (prefixWord ++ tailWord_3549776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549776).length < 2 ^ (prefixWord ++ tailWord_3549776).sum := by decide
  have hdescent : baseEnd_3549776 < baseStart_3549776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549844 : List Nat := [2, 4, 2, 2, 1, 1, 2, 1, 4, 2, 2]
def baseStart_3549844 : Nat := 118140960795 + 3549844 * 2 ^ 59
def prefixEnd_3549844 : Nat := 4983230072969 + 3 ^ 40 * 3549844 * 2
def baseEnd_3549844 : Nat := 1822776220479114452724571

theorem tailTrace_3549844 : CollatzResearch.WordTrace tailWord_3549844 prefixEnd_3549844 1822776220479114452724571 := by
  unfold tailWord_3549844
  simp only [CollatzResearch.WordTrace]
  refine ⟨64736723675764463966540293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86315631567685951955387057 64736723675764463966540293)
  ·
    refine ⟨12138135689205836993726305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64736723675764463966540293 12138135689205836993726305)
    ·
      refine ⟨9103601766904377745294729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12138135689205836993726305 9103601766904377745294729)
      ·
        refine ⟨6827701325178283308971047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9103601766904377745294729 6827701325178283308971047)
        ·
          refine ⟨10241551987767424963456571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6827701325178283308971047 10241551987767424963456571)
          ·
            refine ⟨15362327981651137445184857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10241551987767424963456571 15362327981651137445184857)
            ·
              refine ⟨11521745986238353083888643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15362327981651137445184857 11521745986238353083888643)
              ·
                refine ⟨17282618979357529625832965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11521745986238353083888643 17282618979357529625832965)
                ·
                  refine ⟨3240491058629536804843681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17282618979357529625832965 3240491058629536804843681)
                  ·
                    refine ⟨2430368293972152603632761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3240491058629536804843681 2430368293972152603632761)
                    ·
                      refine ⟨1822776220479114452724571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2430368293972152603632761 1822776220479114452724571)
                      ·
                        rfl

theorem cell23_3549844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_3549844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3549844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3549844 prefixEnd_3549844 := by exact prefixLift 3549844
  have htrace : WordTrace (prefixWord ++ tailWord_3549844) baseStart_3549844 baseEnd_3549844 := by
    simpa [prefixWord, tailWord_3549844, baseEnd_3549844] using wordTrace_append hprefix tailTrace_3549844
  have hstable : (prefixWord ++ tailWord_3549844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549844).length < 2 ^ (prefixWord ++ tailWord_3549844).sum := by decide
  have hdescent : baseEnd_3549844 < baseStart_3549844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549903 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 5, 4, 3]
def baseStart_3549903 : Nat := 118140960795 + 3549903 * 2 ^ 59
def prefixEnd_3549903 : Nat := 4983230072969 + 3 ^ 40 * 3549903 * 2
def baseEnd_3549903 : Nat := 1822806515837729721886799

theorem tailTrace_3549903 : CollatzResearch.WordTrace tailWord_3549903 prefixEnd_3549903 1822806515837729721886799 := by
  unfold tailWord_3549903
  simp only [CollatzResearch.WordTrace]
  refine ⟨129475599258315181009478363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86317066172210120672985575 129475599258315181009478363)
  ·
    refine ⟨194213398887472771514217545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129475599258315181009478363 194213398887472771514217545)
    ·
      refine ⟨145660049165604578635663159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194213398887472771514217545 145660049165604578635663159)
      ·
        refine ⟨218490073748406867953494739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145660049165604578635663159 218490073748406867953494739)
        ·
          refine ⟨327735110622610301930242109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218490073748406867953494739 327735110622610301930242109)
          ·
            refine ⟨122900666483478863223840791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 327735110622610301930242109 122900666483478863223840791)
            ·
              refine ⟨184350999725218294835761187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122900666483478863223840791 184350999725218294835761187)
              ·
                refine ⟨276526499587827442253641781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184350999725218294835761187 276526499587827442253641781)
                ·
                  refine ⟨25924359336358822711278917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 276526499587827442253641781 25924359336358822711278917)
                  ·
                    refine ⟨4860817375567279258364797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25924359336358822711278917 4860817375567279258364797)
                    ·
                      refine ⟨1822806515837729721886799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4860817375567279258364797 1822806515837729721886799)
                      ·
                        rfl

theorem cell23_3549903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 4, 3].length) (baseStart_3549903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3549903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3549903 prefixEnd_3549903 := by exact prefixLift 3549903
  have htrace : WordTrace (prefixWord ++ tailWord_3549903) baseStart_3549903 baseEnd_3549903 := by
    simpa [prefixWord, tailWord_3549903, baseEnd_3549903] using wordTrace_append hprefix tailTrace_3549903
  have hstable : (prefixWord ++ tailWord_3549903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549903).length < 2 ^ (prefixWord ++ tailWord_3549903).sum := by decide
  have hdescent : baseEnd_3549903 < baseStart_3549903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3549967 : List Nat := [1, 1, 2, 1, 1, 1, 8, 1, 3, 1, 3]
def baseStart_3549967 : Nat := 118140960795 + 3549967 * 2 ^ 59
def prefixEnd_3549967 : Nat := 4983230072969 + 3 ^ 40 * 3549967 * 2
def baseEnd_3549967 : Nat := 1822839378599617471486505

theorem tailTrace_3549967 : CollatzResearch.WordTrace tailWord_3549967 prefixEnd_3549967 1822839378599617471486505 := by
  unfold tailWord_3549967
  simp only [CollatzResearch.WordTrace]
  refine ⟨129477933530083319939808155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86318622353388879959872103 129477933530083319939808155)
  ·
    refine ⟨194216900295124979909712233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129477933530083319939808155 194216900295124979909712233)
    ·
      refine ⟨145662675221343734932284175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194216900295124979909712233 145662675221343734932284175)
      ·
        refine ⟨218494012832015602398426263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145662675221343734932284175 218494012832015602398426263)
        ·
          refine ⟨327741019248023403597639395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218494012832015602398426263 327741019248023403597639395)
          ·
            refine ⟨491611528872035105396459093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327741019248023403597639395 491611528872035105396459093)
            ·
              refine ⟨5761072603969161391364755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 491611528872035105396459093 5761072603969161391364755)
              ·
                refine ⟨8641608905953742087047133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5761072603969161391364755 8641608905953742087047133)
                ·
                  refine ⟨3240603339732653282642675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8641608905953742087047133 3240603339732653282642675)
                  ·
                    refine ⟨4860905009598979923964013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3240603339732653282642675 4860905009598979923964013)
                    ·
                      refine ⟨1822839378599617471486505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4860905009598979923964013 1822839378599617471486505)
                      ·
                        rfl

theorem cell23_3549967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 1, 3, 1, 3].length) (baseStart_3549967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3549967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3549967 prefixEnd_3549967 := by exact prefixLift 3549967
  have htrace : WordTrace (prefixWord ++ tailWord_3549967) baseStart_3549967 baseEnd_3549967 := by
    simpa [prefixWord, tailWord_3549967, baseEnd_3549967] using wordTrace_append hprefix tailTrace_3549967
  have hstable : (prefixWord ++ tailWord_3549967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3549967).length < 2 ^ (prefixWord ++ tailWord_3549967).sum := by decide
  have hdescent : baseEnd_3549967 < baseStart_3549967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3549967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550040 : List Nat := [2, 1, 2, 2, 1, 1, 1, 2, 5, 3, 3]
def baseStart_3550040 : Nat := 118140960795 + 3550040 * 2 ^ 59
def prefixEnd_3550040 : Nat := 4983230072969 + 3 ^ 40 * 3550040 * 2
def baseEnd_3550040 : Nat := 1822876862687395685873669

theorem tailTrace_3550040 : CollatzResearch.WordTrace tailWord_3550040 prefixEnd_3550040 1822876862687395685873669 := by
  unfold tailWord_3550040
  simp only [CollatzResearch.WordTrace]
  refine ⟨64740298029409426703607787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86320397372545902271477049 64740298029409426703607787)
  ·
    refine ⟨97110447044114140055411681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64740298029409426703607787 97110447044114140055411681)
    ·
      refine ⟨72832835283085605041558761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97110447044114140055411681 72832835283085605041558761)
      ·
        refine ⟨54624626462314203781169071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72832835283085605041558761 54624626462314203781169071)
        ·
          refine ⟨81936939693471305671753607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54624626462314203781169071 81936939693471305671753607)
          ·
            refine ⟨122905409540206958507630411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81936939693471305671753607 122905409540206958507630411)
            ·
              refine ⟨184358114310310437761445617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122905409540206958507630411 184358114310310437761445617)
              ·
                refine ⟨138268585732732828321084213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184358114310310437761445617 138268585732732828321084213)
                ·
                  refine ⟨12962679912443702655101645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 138268585732732828321084213 12962679912443702655101645)
                  ·
                    refine ⟨4861004967166388495663117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12962679912443702655101645 4861004967166388495663117)
                    ·
                      refine ⟨1822876862687395685873669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4861004967166388495663117 1822876862687395685873669)
                      ·
                        rfl

theorem cell23_3550040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 5, 3, 3].length) (baseStart_3550040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3550040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3550040 prefixEnd_3550040 := by exact prefixLift 3550040
  have htrace : WordTrace (prefixWord ++ tailWord_3550040) baseStart_3550040 baseEnd_3550040 := by
    simpa [prefixWord, tailWord_3550040, baseEnd_3550040] using wordTrace_append hprefix tailTrace_3550040
  have hstable : (prefixWord ++ tailWord_3550040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550040).length < 2 ^ (prefixWord ++ tailWord_3550040).sum := by decide
  have hdescent : baseEnd_3550040 < baseStart_3550040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550044 : List Nat := [2, 2, 4, 2, 1, 2, 1, 1, 3, 2, 3]
def baseStart_3550044 : Nat := 118140960795 + 3550044 * 2 ^ 59
def prefixEnd_3550044 : Nat := 4983230072969 + 3 ^ 40 * 3550044 * 2
def baseEnd_3550044 : Nat := 1822878916610013670223651

theorem tailTrace_3550044 : CollatzResearch.WordTrace tailWord_3550044 prefixEnd_3550044 1822878916610013670223651 := by
  unfold tailWord_3550044
  simp only [CollatzResearch.WordTrace]
  refine ⟨64740370975402181045180593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86320494633869574726907457 64740370975402181045180593)
  ·
    refine ⟨48555278231551635783885445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64740370975402181045180593 48555278231551635783885445)
    ·
      refine ⟨9104114668415931709478521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48555278231551635783885445 9104114668415931709478521)
      ·
        refine ⟨6828086001311948782108891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9104114668415931709478521 6828086001311948782108891)
        ·
          refine ⟨10242129001967923173163337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6828086001311948782108891 10242129001967923173163337)
          ·
            refine ⟨7681596751475942379872503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10242129001967923173163337 7681596751475942379872503)
            ·
              refine ⟨11522395127213913569808755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7681596751475942379872503 11522395127213913569808755)
              ·
                refine ⟨17283592690820870354713133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11522395127213913569808755 17283592690820870354713133)
                ·
                  refine ⟨6481347259057826383017425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17283592690820870354713133 6481347259057826383017425)
                  ·
                    refine ⟨4861010444293369787263069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6481347259057826383017425 4861010444293369787263069)
                    ·
                      refine ⟨1822878916610013670223651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4861010444293369787263069 1822878916610013670223651)
                      ·
                        rfl

theorem cell23_3550044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_3550044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3550044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3550044 prefixEnd_3550044 := by exact prefixLift 3550044
  have htrace : WordTrace (prefixWord ++ tailWord_3550044) baseStart_3550044 baseEnd_3550044 := by
    simpa [prefixWord, tailWord_3550044, baseEnd_3550044] using wordTrace_append hprefix tailTrace_3550044
  have hstable : (prefixWord ++ tailWord_3550044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550044).length < 2 ^ (prefixWord ++ tailWord_3550044).sum := by decide
  have hdescent : baseEnd_3550044 < baseStart_3550044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550125 : List Nat := [1, 5, 2, 3, 1, 2, 1, 2, 2, 1, 3]
def baseStart_3550125 : Nat := 118140960795 + 3550125 * 2 ^ 59
def prefixEnd_3550125 : Nat := 4983230072969 + 3 ^ 40 * 3550125 * 2
def baseEnd_3550125 : Nat := 1822920508543027853310779

theorem tailTrace_3550125 : CollatzResearch.WordTrace tailWord_3550125 prefixEnd_3550125 1822920508543027853310779 := by
  unfold tailWord_3550125
  simp only [CollatzResearch.WordTrace]
  refine ⟨129483696263510912924059829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86322464175673941949373219 129483696263510912924059829)
  ·
    refine ⟨12139096524704148086630609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 129483696263510912924059829 12139096524704148086630609)
    ·
      refine ⟨9104322393528111064972957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12139096524704148086630609 9104322393528111064972957)
      ·
        refine ⟨3414120897573041649364859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9104322393528111064972957 3414120897573041649364859)
        ·
          refine ⟨5121181346359562474047289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3414120897573041649364859 5121181346359562474047289)
          ·
            refine ⟨3840886009769671855535467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5121181346359562474047289 3840886009769671855535467)
            ·
              refine ⟨5761329014654507783303201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3840886009769671855535467 5761329014654507783303201)
              ·
                refine ⟨4320996760990880837477401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5761329014654507783303201 4320996760990880837477401)
                ·
                  refine ⟨3240747570743160628108051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4320996760990880837477401 3240747570743160628108051)
                  ·
                    refine ⟨4861121356114740942162077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3240747570743160628108051 4861121356114740942162077)
                    ·
                      refine ⟨1822920508543027853310779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4861121356114740942162077 1822920508543027853310779)
                      ·
                        rfl

theorem cell23_3550125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_3550125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3550125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3550125 prefixEnd_3550125 := by exact prefixLift 3550125
  have htrace : WordTrace (prefixWord ++ tailWord_3550125) baseStart_3550125 baseEnd_3550125 := by
    simpa [prefixWord, tailWord_3550125, baseEnd_3550125] using wordTrace_append hprefix tailTrace_3550125
  have hstable : (prefixWord ++ tailWord_3550125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550125).length < 2 ^ (prefixWord ++ tailWord_3550125).sum := by decide
  have hdescent : baseEnd_3550125 < baseStart_3550125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550137 : List Nat := [1, 2, 1, 4, 2, 3, 2, 1, 7]
def baseStart_3550137 : Nat := 118140960795 + 3550137 * 2 ^ 59
def prefixEnd_3550137 : Nat := 4983230072969 + 3 ^ 40 * 3550137 * 2
def baseEnd_3550137 : Nat := 202547407812320200706747

theorem tailTrace_3550137 : CollatzResearch.WordTrace tailWord_3550137 prefixEnd_3550137 202547407812320200706747 := by
  unfold tailWord_3550137
  simp only [CollatzResearch.WordTrace]
  refine ⟨129484133939467438973496665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86322755959644959315664443 129484133939467438973496665)
  ·
    refine ⟨97113100454600579230122499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129484133939467438973496665 97113100454600579230122499)
    ·
      refine ⟨145669650681900868845183749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97113100454600579230122499 145669650681900868845183749)
      ·
        refine ⟨27313059502856412908471953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145669650681900868845183749 27313059502856412908471953)
        ·
          refine ⟨20484794627142309681353965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27313059502856412908471953 20484794627142309681353965)
          ·
            refine ⟨7681797985178366130507737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20484794627142309681353965 7681797985178366130507737)
            ·
              refine ⟨5761348488883774597880803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7681797985178366130507737 5761348488883774597880803)
              ·
                refine ⟨8642022733325661896821205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5761348488883774597880803 8642022733325661896821205)
                ·
                  refine ⟨202547407812320200706747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8642022733325661896821205 202547407812320200706747)
                  ·
                    rfl

theorem cell23_3550137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 1, 7].length) (baseStart_3550137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3550137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3550137 prefixEnd_3550137 := by exact prefixLift 3550137
  have htrace : WordTrace (prefixWord ++ tailWord_3550137) baseStart_3550137 baseEnd_3550137 := by
    simpa [prefixWord, tailWord_3550137, baseEnd_3550137] using wordTrace_append hprefix tailTrace_3550137
  have hstable : (prefixWord ++ tailWord_3550137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550137).length < 2 ^ (prefixWord ++ tailWord_3550137).sum := by decide
  have hdescent : baseEnd_3550137 < baseStart_3550137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550160 : List Nat := [2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 5]
def baseStart_3550160 : Nat := 118140960795 + 3550160 * 2 ^ 59
def prefixEnd_3550160 : Nat := 4983230072969 + 3 ^ 40 * 3550160 * 2
def baseEnd_3550160 : Nat := 1822938480365935216373117

theorem tailTrace_3550160 : CollatzResearch.WordTrace tailWord_3550160 prefixEnd_3550160 1822938480365935216373117 := by
  unfold tailWord_3550160
  simp only [CollatzResearch.WordTrace]
  refine ⟨64742486409192056950791967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86323315212256075934389289 64742486409192056950791967)
  ·
    refine ⟨97113729613788085426187951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64742486409192056950791967 97113729613788085426187951)
    ·
      refine ⟨145670594420682128139281927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97113729613788085426187951 145670594420682128139281927)
      ·
        refine ⟨218505891631023192208922891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145670594420682128139281927 218505891631023192208922891)
        ·
          refine ⟨327758837446534788313384337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218505891631023192208922891 327758837446534788313384337)
          ·
            refine ⟨245819128084901091235038253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 327758837446534788313384337 245819128084901091235038253)
            ·
              refine ⟨92182173031837909213139345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 245819128084901091235038253 92182173031837909213139345)
              ·
                refine ⟨69136629773878431909854509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92182173031837909213139345 69136629773878431909854509)
                ·
                  refine ⟨25926236165204411966195441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69136629773878431909854509 25926236165204411966195441)
                  ·
                    refine ⟨19444677123903308974646581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25926236165204411966195441 19444677123903308974646581)
                    ·
                      refine ⟨1822938480365935216373117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19444677123903308974646581 1822938480365935216373117)
                      ·
                        rfl

theorem cell23_3550160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 5].length) (baseStart_3550160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3550160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3550160 prefixEnd_3550160 := by exact prefixLift 3550160
  have htrace : WordTrace (prefixWord ++ tailWord_3550160) baseStart_3550160 baseEnd_3550160 := by
    simpa [prefixWord, tailWord_3550160, baseEnd_3550160] using wordTrace_append hprefix tailTrace_3550160
  have hstable : (prefixWord ++ tailWord_3550160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550160).length < 2 ^ (prefixWord ++ tailWord_3550160).sum := by decide
  have hdescent : baseEnd_3550160 < baseStart_3550160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550244 : List Nat := [2, 3, 1, 4, 1, 1, 1, 4, 6]
def baseStart_3550244 : Nat := 118140960795 + 3550244 * 2 ^ 59
def prefixEnd_3550244 : Nat := 4983230072969 + 3 ^ 40 * 3550244 * 2
def baseEnd_3550244 : Nat := 202553512526768098635859

theorem tailTrace_3550244 : CollatzResearch.WordTrace tailWord_3550244 prefixEnd_3550244 202553512526768098635859 := by
  unfold tailWord_3550244
  simp only [CollatzResearch.WordTrace]
  refine ⟨64744018275039898123820893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86325357700053197498427857 64744018275039898123820893)
  ·
    refine ⟨24279006853139961796432835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64744018275039898123820893 24279006853139961796432835)
    ·
      refine ⟨36418510279709942694649253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24279006853139961796432835 36418510279709942694649253)
      ·
        refine ⟨6828470677445614255246735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36418510279709942694649253 6828470677445614255246735)
        ·
          refine ⟨10242706016168421382870103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6828470677445614255246735 10242706016168421382870103)
          ·
            refine ⟨15364059024252632074305155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10242706016168421382870103 15364059024252632074305155)
            ·
              refine ⟨23046088536378948111457733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15364059024252632074305155 23046088536378948111457733)
              ·
                refine ⟨4321141600571052770898325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23046088536378948111457733 4321141600571052770898325)
                ·
                  refine ⟨202553512526768098635859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4321141600571052770898325 202553512526768098635859)
                  ·
                    rfl

theorem cell23_3550244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 4, 6].length) (baseStart_3550244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3550244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3550244 prefixEnd_3550244 := by exact prefixLift 3550244
  have htrace : WordTrace (prefixWord ++ tailWord_3550244) baseStart_3550244 baseEnd_3550244 := by
    simpa [prefixWord, tailWord_3550244, baseEnd_3550244] using wordTrace_append hprefix tailTrace_3550244
  have hstable : (prefixWord ++ tailWord_3550244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550244).length < 2 ^ (prefixWord ++ tailWord_3550244).sum := by decide
  have hdescent : baseEnd_3550244 < baseStart_3550244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550257 : List Nat := [1, 2, 2, 3, 1, 2, 1, 1, 5, 5]
def baseStart_3550257 : Nat := 118140960795 + 3550257 * 2 ^ 59
def prefixEnd_3550257 : Nat := 4983230072969 + 3 ^ 40 * 3550257 * 2
def baseEnd_3550257 : Nat := 607662762663140445620057

theorem tailTrace_3550257 : CollatzResearch.WordTrace tailWord_3550257 prefixEnd_3550257 607662762663140445620057 := by
  unfold tailWord_3550257
  simp only [CollatzResearch.WordTrace]
  refine ⟨129488510699032699467865025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86325673799355132978576683 129488510699032699467865025)
  ·
    refine ⟨97116383024274524600898769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129488510699032699467865025 97116383024274524600898769)
    ·
      refine ⟨72837287268205893450674077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97116383024274524600898769 72837287268205893450674077)
      ·
        refine ⟨27313982725577210044002779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72837287268205893450674077 27313982725577210044002779)
        ·
          refine ⟨40970974088365815066004169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27313982725577210044002779 40970974088365815066004169)
          ·
            refine ⟨30728230566274361299503127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40970974088365815066004169 30728230566274361299503127)
            ·
              refine ⟨46092345849411541949254691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30728230566274361299503127 46092345849411541949254691)
              ·
                refine ⟨69138518774117312923882037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46092345849411541949254691 69138518774117312923882037)
                ·
                  refine ⟨6481736135073498086613941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69138518774117312923882037 6481736135073498086613941)
                  ·
                    refine ⟨607662762663140445620057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6481736135073498086613941 607662762663140445620057)
                    ·
                      rfl

theorem cell23_3550257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 5, 5].length) (baseStart_3550257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3550257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3550257 prefixEnd_3550257 := by exact prefixLift 3550257
  have htrace : WordTrace (prefixWord ++ tailWord_3550257) baseStart_3550257 baseEnd_3550257 := by
    simpa [prefixWord, tailWord_3550257, baseEnd_3550257] using wordTrace_append hprefix tailTrace_3550257
  have hstable : (prefixWord ++ tailWord_3550257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550257).length < 2 ^ (prefixWord ++ tailWord_3550257).sum := by decide
  have hdescent : baseEnd_3550257 < baseStart_3550257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550304 : List Nat := [2, 1, 1, 3, 2, 2, 3, 1, 4, 4]
def baseStart_3550304 : Nat := 118140960795 + 3550304 * 2 ^ 59
def prefixEnd_3550304 : Nat := 4983230072969 + 3 ^ 40 * 3550304 * 2
def baseEnd_3550304 : Nat := 607670807193394217657485

theorem tailTrace_3550304 : CollatzResearch.WordTrace tailWord_3550304 prefixEnd_3550304 607670807193394217657485 := by
  unfold tailWord_3550304
  simp only [CollatzResearch.WordTrace]
  refine ⟨64745112464931213247412983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86326816619908284329883977 64745112464931213247412983)
  ·
    refine ⟨97117668697396819871119475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64745112464931213247412983 97117668697396819871119475)
    ·
      refine ⟨145676503046095229806679213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97117668697396819871119475 145676503046095229806679213)
      ·
        refine ⟨54628688642285711177504705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145676503046095229806679213 54628688642285711177504705)
        ·
          refine ⟨40971516481714283383128529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54628688642285711177504705 40971516481714283383128529)
          ·
            refine ⟨30728637361285712537346397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40971516481714283383128529 30728637361285712537346397)
            ·
              refine ⟨11523239010482142201504899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30728637361285712537346397 11523239010482142201504899)
              ·
                refine ⟨17284858515723213302257349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11523239010482142201504899 17284858515723213302257349)
                ·
                  refine ⟨3240910971698102494173253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17284858515723213302257349 3240910971698102494173253)
                  ·
                    refine ⟨607670807193394217657485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3240910971698102494173253 607670807193394217657485)
                    ·
                      rfl

theorem cell23_3550304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 4, 4].length) (baseStart_3550304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3550304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3550304 prefixEnd_3550304 := by exact prefixLift 3550304
  have htrace : WordTrace (prefixWord ++ tailWord_3550304) baseStart_3550304 baseEnd_3550304 := by
    simpa [prefixWord, tailWord_3550304, baseEnd_3550304] using wordTrace_append hprefix tailTrace_3550304
  have hstable : (prefixWord ++ tailWord_3550304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550304).length < 2 ^ (prefixWord ++ tailWord_3550304).sum := by decide
  have hdescent : baseEnd_3550304 < baseStart_3550304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550307 : List Nat := [1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 6]
def baseStart_3550307 : Nat := 118140960795 + 3550307 * 2 ^ 59
def prefixEnd_3550307 : Nat := 4983230072969 + 3 ^ 40 * 3550307 * 2
def baseEnd_3550307 : Nat := 1823013962022146141234941

theorem tailTrace_3550307 : CollatzResearch.WordTrace tailWord_3550307 prefixEnd_3550307 1823013962022146141234941 := by
  unfold tailWord_3550307
  simp only [CollatzResearch.WordTrace]
  refine ⟨129490334348851558007185175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86326889565901038671456783 129490334348851558007185175)
  ·
    refine ⟨194235501523277337010777763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129490334348851558007185175 194235501523277337010777763)
    ·
      refine ⟨291353252284916005516166645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194235501523277337010777763 291353252284916005516166645)
      ·
        refine ⟨27314367401710875517140623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 291353252284916005516166645 27314367401710875517140623)
        ·
          refine ⟨40971551102566313275710935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27314367401710875517140623 40971551102566313275710935)
          ·
            refine ⟨61457326653849469913566403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40971551102566313275710935 61457326653849469913566403)
            ·
              refine ⟨92185989980774204870349605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61457326653849469913566403 92185989980774204870349605)
              ·
                refine ⟨17284873121395163413190551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92185989980774204870349605 17284873121395163413190551)
                ·
                  refine ⟨25927309682092745119785827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17284873121395163413190551 25927309682092745119785827)
                  ·
                    refine ⟨38890964523139117679678741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25927309682092745119785827 38890964523139117679678741)
                    ·
                      refine ⟨1823013962022146141234941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38890964523139117679678741 1823013962022146141234941)
                      ·
                        rfl

theorem cell23_3550307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_3550307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3550307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3550307 prefixEnd_3550307 := by exact prefixLift 3550307
  have htrace : WordTrace (prefixWord ++ tailWord_3550307) baseStart_3550307 baseEnd_3550307 := by
    simpa [prefixWord, tailWord_3550307, baseEnd_3550307] using wordTrace_append hprefix tailTrace_3550307
  have hstable : (prefixWord ++ tailWord_3550307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550307).length < 2 ^ (prefixWord ++ tailWord_3550307).sum := by decide
  have hdescent : baseEnd_3550307 < baseStart_3550307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550314 : List Nat := [3, 1, 3, 2, 2, 1, 1, 1, 3, 1, 5]
def baseStart_3550314 : Nat := 118140960795 + 3550314 * 2 ^ 59
def prefixEnd_3550314 : Nat := 4983230072969 + 3 ^ 40 * 3550314 * 2
def baseEnd_3550314 : Nat := 1823017556386727613847409

theorem tailTrace_3550314 : CollatzResearch.WordTrace tailWord_3550314 prefixEnd_3550314 1823017556386727613847409 := by
  unfold tailWord_3550314
  simp only [CollatzResearch.WordTrace]
  refine ⟨32372647414956549550672499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86327059773217465468459997 32372647414956549550672499)
  ·
    refine ⟨48558971122434824326008749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32372647414956549550672499 48558971122434824326008749)
    ·
      refine ⟨18209614170913059122253281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48558971122434824326008749 18209614170913059122253281)
      ·
        refine ⟨13657210628184794341689961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18209614170913059122253281 13657210628184794341689961)
        ·
          refine ⟨10242907971138595756267471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13657210628184794341689961 10242907971138595756267471)
          ·
            refine ⟨15364361956707893634401207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10242907971138595756267471 15364361956707893634401207)
            ·
              refine ⟨23046542935061840451601811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15364361956707893634401207 23046542935061840451601811)
              ·
                refine ⟨34569814402592760677402717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23046542935061840451601811 34569814402592760677402717)
                ·
                  refine ⟨12963680400972285254026019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34569814402592760677402717 12963680400972285254026019)
                  ·
                    refine ⟨19445520601458427881039029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12963680400972285254026019 19445520601458427881039029)
                    ·
                      refine ⟨1823017556386727613847409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19445520601458427881039029 1823017556386727613847409)
                      ·
                        rfl

theorem cell23_3550314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_3550314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3550314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3550314 prefixEnd_3550314 := by exact prefixLift 3550314
  have htrace : WordTrace (prefixWord ++ tailWord_3550314) baseStart_3550314 baseEnd_3550314 := by
    simpa [prefixWord, tailWord_3550314, baseEnd_3550314] using wordTrace_append hprefix tailTrace_3550314
  have hstable : (prefixWord ++ tailWord_3550314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550314).length < 2 ^ (prefixWord ++ tailWord_3550314).sum := by decide
  have hdescent : baseEnd_3550314 < baseStart_3550314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550345 : List Nat := [1, 2, 1, 1, 4, 3, 3, 3, 1, 2, 2]
def baseStart_3550345 : Nat := 118140960795 + 3550345 * 2 ^ 59
def prefixEnd_3550345 : Nat := 4983230072969 + 3 ^ 40 * 3550345 * 2
def baseEnd_3550345 : Nat := 1823033474287016992559767

theorem tailTrace_3550345 : CollatzResearch.WordTrace tailWord_3550345 prefixEnd_3550345 1823033474287016992559767 := by
  unfold tailWord_3550345
  simp only [CollatzResearch.WordTrace]
  refine ⟨129491720322713890497068489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86327813548475926998045659 129491720322713890497068489)
  ·
    refine ⟨97118790242035417872801367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129491720322713890497068489 97118790242035417872801367)
    ·
      refine ⟨145678185363053126809202051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97118790242035417872801367 145678185363053126809202051)
      ·
        refine ⟨218517278044579690213803077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145678185363053126809202051 218517278044579690213803077)
        ·
          refine ⟨40971989633358691915088077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 218517278044579690213803077 40971989633358691915088077)
          ·
            refine ⟨15364496112509509468158029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40971989633358691915088077 15364496112509509468158029)
            ·
              refine ⟨5761686042191066050559261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15364496112509509468158029 5761686042191066050559261)
              ·
                refine ⟨2160632265821649768959723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5761686042191066050559261 2160632265821649768959723)
                ·
                  refine ⟨3240948398732474653439585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2160632265821649768959723 3240948398732474653439585)
                  ·
                    refine ⟨2430711299049355990079689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3240948398732474653439585 2430711299049355990079689)
                    ·
                      refine ⟨1823033474287016992559767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2430711299049355990079689 1823033474287016992559767)
                      ·
                        rfl

theorem cell23_3550345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 3, 1, 2, 2].length) (baseStart_3550345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3550345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3550345 prefixEnd_3550345 := by exact prefixLift 3550345
  have htrace : WordTrace (prefixWord ++ tailWord_3550345) baseStart_3550345 baseEnd_3550345 := by
    simpa [prefixWord, tailWord_3550345, baseEnd_3550345] using wordTrace_append hprefix tailTrace_3550345
  have hstable : (prefixWord ++ tailWord_3550345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550345).length < 2 ^ (prefixWord ++ tailWord_3550345).sum := by decide
  have hdescent : baseEnd_3550345 < baseStart_3550345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550413 : List Nat := [1, 6, 2, 2, 1, 2, 2, 2, 1, 2, 2]
def baseStart_3550413 : Nat := 118140960795 + 3550413 * 2 ^ 59
def prefixEnd_3550413 : Nat := 4983230072969 + 3 ^ 40 * 3550413 * 2
def baseEnd_3550413 : Nat := 1823068390971522726509455

theorem tailTrace_3550413 : CollatzResearch.WordTrace tailWord_3550413 prefixEnd_3550413 1823068390971522726509455 := by
  unfold tailWord_3550413
  simp only [CollatzResearch.WordTrace]
  refine ⟨129494200486467538110543893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86329466990978358740362595 129494200486467538110543893)
  ·
    refine ⟨6070040647803165848931745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 129494200486467538110543893 6070040647803165848931745)
    ·
      refine ⟨4552530485852374386698809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6070040647803165848931745 4552530485852374386698809)
      ·
        refine ⟨3414397864389280790024107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4552530485852374386698809 3414397864389280790024107)
        ·
          refine ⟨5121596796583921185036161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3414397864389280790024107 5121596796583921185036161)
          ·
            refine ⟨3841197597437940888777121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5121596796583921185036161 3841197597437940888777121)
            ·
              refine ⟨2880898198078455666582841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3841197597437940888777121 2880898198078455666582841)
              ·
                refine ⟨2160673648558841749937131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2880898198078455666582841 2160673648558841749937131)
                ·
                  refine ⟨3241010472838262624905697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2160673648558841749937131 3241010472838262624905697)
                  ·
                    refine ⟨2430757854628696968679273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3241010472838262624905697 2430757854628696968679273)
                    ·
                      refine ⟨1823068390971522726509455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2430757854628696968679273 1823068390971522726509455)
                      ·
                        rfl

theorem cell23_3550413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_3550413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3550413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3550413 prefixEnd_3550413 := by exact prefixLift 3550413
  have htrace : WordTrace (prefixWord ++ tailWord_3550413) baseStart_3550413 baseEnd_3550413 := by
    simpa [prefixWord, tailWord_3550413, baseEnd_3550413] using wordTrace_append hprefix tailTrace_3550413
  have hstable : (prefixWord ++ tailWord_3550413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550413).length < 2 ^ (prefixWord ++ tailWord_3550413).sum := by decide
  have hdescent : baseEnd_3550413 < baseStart_3550413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550421 : List Nat := [1, 3, 2, 4, 1, 1, 1, 1, 2, 4, 3]
def baseStart_3550421 : Nat := 118140960795 + 3550421 * 2 ^ 59
def prefixEnd_3550421 : Nat := 4983230072969 + 3 ^ 40 * 3550421 * 2
def baseEnd_3550421 : Nat := 1823072498816758695209417

theorem tailTrace_3550421 : CollatzResearch.WordTrace tailWord_3550421 prefixEnd_3550421 1823072498816758695209417 := by
  unfold tailWord_3550421
  simp only [CollatzResearch.WordTrace]
  refine ⟨129494492270438555476835117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86329661513625703651223411 129494492270438555476835117)
  ·
    refine ⟨48560434601414458303813169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129494492270438555476835117 48560434601414458303813169)
    ·
      refine ⟨36420325951060843727859877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48560434601414458303813169 36420325951060843727859877)
      ·
        refine ⟨6828811115823908198973727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36420325951060843727859877 6828811115823908198973727)
        ·
          refine ⟨10243216673735862298460591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6828811115823908198973727 10243216673735862298460591)
          ·
            refine ⟨15364825010603793447690887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10243216673735862298460591 15364825010603793447690887)
            ·
              refine ⟨23047237515905690171536331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15364825010603793447690887 23047237515905690171536331)
              ·
                refine ⟨34570856273858535257304497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23047237515905690171536331 34570856273858535257304497)
                ·
                  refine ⟨25928142205393901442978373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34570856273858535257304497 25928142205393901442978373)
                  ·
                    refine ⟨4861526663511356520558445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25928142205393901442978373 4861526663511356520558445)
                    ·
                      refine ⟨1823072498816758695209417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4861526663511356520558445 1823072498816758695209417)
                      ·
                        rfl

theorem cell23_3550421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_3550421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3550421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3550421 prefixEnd_3550421 := by exact prefixLift 3550421
  have htrace : WordTrace (prefixWord ++ tailWord_3550421) baseStart_3550421 baseEnd_3550421 := by
    simpa [prefixWord, tailWord_3550421, baseEnd_3550421] using wordTrace_append hprefix tailTrace_3550421
  have hstable : (prefixWord ++ tailWord_3550421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550421).length < 2 ^ (prefixWord ++ tailWord_3550421).sum := by decide
  have hdescent : baseEnd_3550421 < baseStart_3550421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550511 : List Nat := [1, 1, 2, 1, 2, 1, 3, 5, 2, 2, 3]
def baseStart_3550511 : Nat := 118140960795 + 3550511 * 2 ^ 59
def prefixEnd_3550511 : Nat := 4983230072969 + 3 ^ 40 * 3550511 * 2
def baseEnd_3550511 : Nat := 1823118712075663343084003

theorem tailTrace_3550511 : CollatzResearch.WordTrace tailWord_3550511 prefixEnd_3550511 1823118712075663343084003 := by
  unfold tailWord_3550511
  simp only [CollatzResearch.WordTrace]
  refine ⟨129497774840112500847611387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86331849893408333898407591 129497774840112500847611387)
  ·
    refine ⟨194246662260168751271417081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129497774840112500847611387 194246662260168751271417081)
    ·
      refine ⟨145684996695126563453562811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194246662260168751271417081 145684996695126563453562811)
      ·
        refine ⟨218527495042689845180344217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145684996695126563453562811 218527495042689845180344217)
        ·
          refine ⟨163895621282017383885258163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218527495042689845180344217 163895621282017383885258163)
          ·
            refine ⟨245843431923026075827887245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163895621282017383885258163 245843431923026075827887245)
            ·
              refine ⟨92191286971134778435457717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 245843431923026075827887245 92191286971134778435457717)
              ·
                refine ⟨8642933153543885478324161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92191286971134778435457717 8642933153543885478324161)
                ·
                  refine ⟨6482199865157914108743121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8642933153543885478324161 6482199865157914108743121)
                  ·
                    refine ⟨4861649898868435581557341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6482199865157914108743121 4861649898868435581557341)
                    ·
                      refine ⟨1823118712075663343084003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4861649898868435581557341 1823118712075663343084003)
                      ·
                        rfl

theorem cell23_3550511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5, 2, 2, 3].length) (baseStart_3550511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3550511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3550511 prefixEnd_3550511 := by exact prefixLift 3550511
  have htrace : WordTrace (prefixWord ++ tailWord_3550511) baseStart_3550511 baseEnd_3550511 := by
    simpa [prefixWord, tailWord_3550511, baseEnd_3550511] using wordTrace_append hprefix tailTrace_3550511
  have hstable : (prefixWord ++ tailWord_3550511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550511).length < 2 ^ (prefixWord ++ tailWord_3550511).sum := by decide
  have hdescent : baseEnd_3550511 < baseStart_3550511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550525 : List Nat := [1, 4, 1, 5, 1, 1, 1, 2, 2, 1, 4]
def baseStart_3550525 : Nat := 118140960795 + 3550525 * 2 ^ 59
def prefixEnd_3550525 : Nat := 4983230072969 + 3 ^ 40 * 3550525 * 2
def baseEnd_3550525 : Nat := 1823125900804826288308939

theorem tailTrace_3550525 : CollatzResearch.WordTrace tailWord_3550525 prefixEnd_3550525 1823125900804826288308939 := by
  unfold tailWord_3550525
  simp only [CollatzResearch.WordTrace]
  refine ⟨129498285462061781238621029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86332190308041187492414019 129498285462061781238621029)
  ·
    refine ⟨24280928524136583982241443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129498285462061781238621029 24280928524136583982241443)
    ·
      refine ⟨36421392786204875973362165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24280928524136583982241443 36421392786204875973362165)
      ·
        refine ⟨3414505573706707122502703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36421392786204875973362165 3414505573706707122502703)
        ·
          refine ⟨5121758360560060683754055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3414505573706707122502703 5121758360560060683754055)
          ·
            refine ⟨7682637540840091025631083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5121758360560060683754055 7682637540840091025631083)
            ·
              refine ⟨11523956311260136538446625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7682637540840091025631083 11523956311260136538446625)
              ·
                refine ⟨8642967233445102403834969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11523956311260136538446625 8642967233445102403834969)
                ·
                  refine ⟨6482225425083826802876227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8642967233445102403834969 6482225425083826802876227)
                  ·
                    refine ⟨9723338137625740204314341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6482225425083826802876227 9723338137625740204314341)
                    ·
                      refine ⟨1823125900804826288308939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9723338137625740204314341 1823125900804826288308939)
                      ·
                        rfl

theorem cell23_3550525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_3550525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3550525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3550525 prefixEnd_3550525 := by exact prefixLift 3550525
  have htrace : WordTrace (prefixWord ++ tailWord_3550525) baseStart_3550525 baseEnd_3550525 := by
    simpa [prefixWord, tailWord_3550525, baseEnd_3550525] using wordTrace_append hprefix tailTrace_3550525
  have hstable : (prefixWord ++ tailWord_3550525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550525).length < 2 ^ (prefixWord ++ tailWord_3550525).sum := by decide
  have hdescent : baseEnd_3550525 < baseStart_3550525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550575 : List Nat := [1, 1, 2, 1, 3, 1, 4, 5, 1, 1, 3]
def baseStart_3550575 : Nat := 118140960795 + 3550575 * 2 ^ 59
def prefixEnd_3550575 : Nat := 4983230072969 + 3 ^ 40 * 3550575 * 2
def baseEnd_3550575 : Nat := 1823151574837551092683709

theorem tailTrace_3550575 : CollatzResearch.WordTrace tailWord_3550575 prefixEnd_3550575 1823151574837551092683709 := by
  unfold tailWord_3550575
  simp only [CollatzResearch.WordTrace]
  refine ⟨129500109111880639777941179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86333406074587093185294119 129500109111880639777941179)
  ·
    refine ⟨194250163667820959666911769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129500109111880639777941179 194250163667820959666911769)
    ·
      refine ⟨145687622750865719750183827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194250163667820959666911769 145687622750865719750183827)
      ·
        refine ⟨218531434126298579625275741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145687622750865719750183827 218531434126298579625275741)
        ·
          refine ⟨81949287797361967359478403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218531434126298579625275741 81949287797361967359478403)
          ·
            refine ⟨122923931696042951039217605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81949287797361967359478403 122923931696042951039217605)
            ·
              refine ⟨23048237193008053319853301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122923931696042951039217605 23048237193008053319853301)
              ·
                refine ⟨2160772236844504998736247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23048237193008053319853301 2160772236844504998736247)
                ·
                  refine ⟨3241158355266757498104371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2160772236844504998736247 3241158355266757498104371)
                  ·
                    refine ⟨4861737532900136247156557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3241158355266757498104371 4861737532900136247156557)
                    ·
                      refine ⟨1823151574837551092683709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4861737532900136247156557 1823151574837551092683709)
                      ·
                        rfl

theorem cell23_3550575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 5, 1, 1, 3].length) (baseStart_3550575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3550575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3550575 prefixEnd_3550575 := by exact prefixLift 3550575
  have htrace : WordTrace (prefixWord ++ tailWord_3550575) baseStart_3550575 baseEnd_3550575 := by
    simpa [prefixWord, tailWord_3550575, baseEnd_3550575] using wordTrace_append hprefix tailTrace_3550575
  have hstable : (prefixWord ++ tailWord_3550575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550575).length < 2 ^ (prefixWord ++ tailWord_3550575).sum := by decide
  have hdescent : baseEnd_3550575 < baseStart_3550575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550618 : List Nat := [3, 1, 1, 4, 1, 1, 1, 3, 3, 2, 3]
def baseStart_3550618 : Nat := 118140960795 + 3550618 * 2 ^ 59
def prefixEnd_3550618 : Nat := 4983230072969 + 3 ^ 40 * 3550618 * 2
def baseEnd_3550618 : Nat := 1823173654505694424446011

theorem tailTrace_3550618 : CollatzResearch.WordTrace tailWord_3550618 prefixEnd_3550618 1823173654505694424446011 := by
  unfold tailWord_3550618
  simp only [CollatzResearch.WordTrace]
  refine ⟨32375419362681214530439127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86334451633816572081171005 32375419362681214530439127)
  ·
    refine ⟨48563129044021821795658691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32375419362681214530439127 48563129044021821795658691)
    ·
      refine ⟨72844693566032732693488037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48563129044021821795658691 72844693566032732693488037)
      ·
        refine ⟨13658380043631137380029007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72844693566032732693488037 13658380043631137380029007)
        ·
          refine ⟨20487570065446706070043511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13658380043631137380029007 20487570065446706070043511)
          ·
            refine ⟨30731355098170059105065267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20487570065446706070043511 30731355098170059105065267)
            ·
              refine ⟨46097032647255088657597901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30731355098170059105065267 46097032647255088657597901)
              ·
                refine ⟨17286387242720658246599213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46097032647255088657597901 17286387242720658246599213)
                ·
                  refine ⟨6482395216020246842474705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17286387242720658246599213 6482395216020246842474705)
                  ·
                    refine ⟨4861796412015185131856029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6482395216020246842474705 4861796412015185131856029)
                    ·
                      refine ⟨1823173654505694424446011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4861796412015185131856029 1823173654505694424446011)
                      ·
                        rfl

theorem cell23_3550618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_3550618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3550618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3550618 prefixEnd_3550618 := by exact prefixLift 3550618
  have htrace : WordTrace (prefixWord ++ tailWord_3550618) baseStart_3550618 baseEnd_3550618 := by
    simpa [prefixWord, tailWord_3550618, baseEnd_3550618] using wordTrace_append hprefix tailTrace_3550618
  have hstable : (prefixWord ++ tailWord_3550618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550618).length < 2 ^ (prefixWord ++ tailWord_3550618).sum := by decide
  have hdescent : baseEnd_3550618 < baseStart_3550618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550632 : List Nat := [2, 1, 6, 1, 2, 1, 1, 3, 1, 1, 4]
def baseStart_3550632 : Nat := 118140960795 + 3550632 * 2 ^ 59
def prefixEnd_3550632 : Nat := 4983230072969 + 3 ^ 40 * 3550632 * 2
def baseEnd_3550632 : Nat := 1823180843234857369670947

theorem tailTrace_3550632 : CollatzResearch.WordTrace tailWord_3550632 prefixEnd_3550632 1823180843234857369670947 := by
  unfold tailWord_3550632
  simp only [CollatzResearch.WordTrace]
  refine ⟨64751094036337069256383075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86334792048449425675177433 64751094036337069256383075)
  ·
    refine ⟨97126641054505603884574613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64751094036337069256383075 97126641054505603884574613)
    ·
      refine ⟨4552811299429950182089435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 97126641054505603884574613 4552811299429950182089435)
      ·
        refine ⟨6829216949144925273134153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4552811299429950182089435 6829216949144925273134153)
        ·
          refine ⟨5121912711858693954850615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6829216949144925273134153 5121912711858693954850615)
          ·
            refine ⟨7682869067788040932275923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5121912711858693954850615 7682869067788040932275923)
            ·
              refine ⟨11524303601682061398413885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7682869067788040932275923 11524303601682061398413885)
              ·
                refine ⟨4321613850630773024405207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11524303601682061398413885 4321613850630773024405207)
                ·
                  refine ⟨6482420775946159536607811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4321613850630773024405207 6482420775946159536607811)
                  ·
                    refine ⟨9723631163919239304911717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6482420775946159536607811 9723631163919239304911717)
                    ·
                      refine ⟨1823180843234857369670947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9723631163919239304911717 1823180843234857369670947)
                      ·
                        rfl

theorem cell23_3550632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_3550632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3550632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3550632 prefixEnd_3550632 := by exact prefixLift 3550632
  have htrace : WordTrace (prefixWord ++ tailWord_3550632) baseStart_3550632 baseEnd_3550632 := by
    simpa [prefixWord, tailWord_3550632, baseEnd_3550632] using wordTrace_append hprefix tailTrace_3550632
  have hstable : (prefixWord ++ tailWord_3550632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550632).length < 2 ^ (prefixWord ++ tailWord_3550632).sum := by decide
  have hdescent : baseEnd_3550632 < baseStart_3550632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550671 : List Nat := [1, 1, 2, 1, 1, 4, 2, 2, 2, 3, 4]
def baseStart_3550671 : Nat := 118140960795 + 3550671 * 2 ^ 59
def prefixEnd_3550671 : Nat := 4983230072969 + 3 ^ 40 * 3550671 * 2
def baseEnd_3550671 : Nat := 1823200868980382717083267

theorem tailTrace_3550671 : CollatzResearch.WordTrace tailWord_3550671 prefixEnd_3550671 1823200868980382717083267 := by
  unfold tailWord_3550671
  simp only [CollatzResearch.WordTrace]
  refine ⟨129503610519532848173435867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86335740346355232115623911 129503610519532848173435867)
  ·
    refine ⟨194255415779299272260153801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129503610519532848173435867 194255415779299272260153801)
    ·
      refine ⟨145691561834474454195115351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194255415779299272260153801 145691561834474454195115351)
      ·
        refine ⟨218537342751711681292673027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145691561834474454195115351 218537342751711681292673027)
        ·
          refine ⟨327806014127567521939009541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218537342751711681292673027 327806014127567521939009541)
          ·
            refine ⟨61463627648918910363564289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 327806014127567521939009541 61463627648918910363564289)
            ·
              refine ⟨46097720736689182772673217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61463627648918910363564289 46097720736689182772673217)
              ·
                refine ⟨34573290552516887079504913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46097720736689182772673217 34573290552516887079504913)
                ·
                  refine ⟨25929967914387665309628685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34573290552516887079504913 25929967914387665309628685)
                  ·
                    refine ⟨9723737967895374491110757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25929967914387665309628685 9723737967895374491110757)
                    ·
                      refine ⟨1823200868980382717083267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9723737967895374491110757 1823200868980382717083267)
                      ·
                        rfl

theorem cell23_3550671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 3, 4].length) (baseStart_3550671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3550671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3550671 prefixEnd_3550671 := by exact prefixLift 3550671
  have htrace : WordTrace (prefixWord ++ tailWord_3550671) baseStart_3550671 baseEnd_3550671 := by
    simpa [prefixWord, tailWord_3550671, baseEnd_3550671] using wordTrace_append hprefix tailTrace_3550671
  have hstable : (prefixWord ++ tailWord_3550671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550671).length < 2 ^ (prefixWord ++ tailWord_3550671).sum := by decide
  have hdescent : baseEnd_3550671 < baseStart_3550671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550711 : List Nat := [1, 1, 3, 1, 1, 1, 1, 7, 7]
def baseStart_3550711 : Nat := 118140960795 + 3550711 * 2 ^ 59
def prefixEnd_3550711 : Nat := 4983230072969 + 3 ^ 40 * 3550711 * 2
def baseEnd_3550711 : Nat := 202580156467395840064787

theorem tailTrace_3550711 : CollatzResearch.WordTrace tailWord_3550711 prefixEnd_3550711 202580156467395840064787 := by
  unfold tailWord_3550711
  simp only [CollatzResearch.WordTrace]
  refine ⟨129505069439387935004891987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86336712959591956669927991 129505069439387935004891987)
  ·
    refine ⟨194257604159081902507337981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129505069439387935004891987 194257604159081902507337981)
    ·
      refine ⟨72846601559655713440251743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194257604159081902507337981 72846601559655713440251743)
      ·
        refine ⟨109269902339483570160377615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72846601559655713440251743 109269902339483570160377615)
        ·
          refine ⟨163904853509225355240566423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109269902339483570160377615 163904853509225355240566423)
          ·
            refine ⟨245857280263838032860849635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163904853509225355240566423 245857280263838032860849635)
            ·
              refine ⟨368785920395757049291274453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245857280263838032860849635 368785920395757049291274453)
              ·
                refine ⟨8643420009275555842764245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 368785920395757049291274453 8643420009275555842764245)
                ·
                  refine ⟨202580156467395840064787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8643420009275555842764245 202580156467395840064787)
                  ·
                    rfl

theorem cell23_3550711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7, 7].length) (baseStart_3550711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3550711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3550711 prefixEnd_3550711 := by exact prefixLift 3550711
  have htrace : WordTrace (prefixWord ++ tailWord_3550711) baseStart_3550711 baseEnd_3550711 := by
    simpa [prefixWord, tailWord_3550711, baseEnd_3550711] using wordTrace_append hprefix tailTrace_3550711
  have hstable : (prefixWord ++ tailWord_3550711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550711).length < 2 ^ (prefixWord ++ tailWord_3550711).sum := by decide
  have hdescent : baseEnd_3550711 < baseStart_3550711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550778 : List Nat := [3, 1, 1, 1, 3, 2, 2, 2, 1, 3, 4]
def baseStart_3550778 : Nat := 118140960795 + 3550778 * 2 ^ 59
def prefixEnd_3550778 : Nat := 4983230072969 + 3 ^ 40 * 3550778 * 2
def baseEnd_3550778 : Nat := 1823255811410413798445275

theorem tailTrace_3550778 : CollatzResearch.WordTrace tailWord_3550778 prefixEnd_3550778 1823255811410413798445275 := by
  unfold tailWord_3550778
  simp only [CollatzResearch.WordTrace]
  refine ⟨32376878282536301361895247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86338342086763470298387325 32376878282536301361895247)
  ·
    refine ⟨48565317423804452042842871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32376878282536301361895247 48565317423804452042842871)
    ·
      refine ⟨72847976135706678064264307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48565317423804452042842871 72847976135706678064264307)
      ·
        refine ⟨109271964203560017096396461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72847976135706678064264307 109271964203560017096396461)
        ·
          refine ⟨40976986576335006411148673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109271964203560017096396461 40976986576335006411148673)
          ·
            refine ⟨30732739932251254808361505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40976986576335006411148673 30732739932251254808361505)
            ·
              refine ⟨23049554949188441106271129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30732739932251254808361505 23049554949188441106271129)
              ·
                refine ⟨17287166211891330829703347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23049554949188441106271129 17287166211891330829703347)
                ·
                  refine ⟨25930749317836996244555021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17287166211891330829703347 25930749317836996244555021)
                  ·
                    refine ⟨9724030994188873591708133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25930749317836996244555021 9724030994188873591708133)
                    ·
                      refine ⟨1823255811410413798445275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9724030994188873591708133 1823255811410413798445275)
                      ·
                        rfl

theorem cell23_3550778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 1, 3, 4].length) (baseStart_3550778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3550778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3550778 prefixEnd_3550778 := by exact prefixLift 3550778
  have htrace : WordTrace (prefixWord ++ tailWord_3550778) baseStart_3550778 baseEnd_3550778 := by
    simpa [prefixWord, tailWord_3550778, baseEnd_3550778] using wordTrace_append hprefix tailTrace_3550778
  have hstable : (prefixWord ++ tailWord_3550778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550778).length < 2 ^ (prefixWord ++ tailWord_3550778).sum := by decide
  have hdescent : baseEnd_3550778 < baseStart_3550778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550812 : List Nat := [2, 2, 4, 1, 2, 1, 1, 2, 2, 4, 2]
def baseStart_3550812 : Nat := 118140960795 + 3550812 * 2 ^ 59
def prefixEnd_3550812 : Nat := 4983230072969 + 3 ^ 40 * 3550812 * 2
def baseEnd_3550812 : Nat := 1823273269752666665420119

theorem tailTrace_3550812 : CollatzResearch.WordTrace tailWord_3550812 prefixEnd_3550812 1823273269752666665420119 := by
  unfold tailWord_3550812
  simp only [CollatzResearch.WordTrace]
  refine ⟨64754376606011014627159345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86339168808014686169545793 64754376606011014627159345)
  ·
    refine ⟨48565782454508260970369509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64754376606011014627159345 48565782454508260970369509)
    ·
      refine ⟨9106084210220298931944283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48565782454508260970369509 9106084210220298931944283)
      ·
        refine ⟨13659126315330448397916425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9106084210220298931944283 13659126315330448397916425)
        ·
          refine ⟨10244344736497836298437319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13659126315330448397916425 10244344736497836298437319)
          ·
            refine ⟨15366517104746754447655979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10244344736497836298437319 15366517104746754447655979)
            ·
              refine ⟨23049775657120131671483969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15366517104746754447655979 23049775657120131671483969)
              ·
                refine ⟨17287331742840098753612977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23049775657120131671483969 17287331742840098753612977)
                ·
                  refine ⟨12965498807130074065209733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17287331742840098753612977 12965498807130074065209733)
                  ·
                    refine ⟨2431031026336888887226825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12965498807130074065209733 2431031026336888887226825)
                    ·
                      refine ⟨1823273269752666665420119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2431031026336888887226825 1823273269752666665420119)
                      ·
                        rfl

theorem cell23_3550812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_3550812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3550812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3550812 prefixEnd_3550812 := by exact prefixLift 3550812
  have htrace : WordTrace (prefixWord ++ tailWord_3550812) baseStart_3550812 baseEnd_3550812 := by
    simpa [prefixWord, tailWord_3550812, baseEnd_3550812] using wordTrace_append hprefix tailTrace_3550812
  have hstable : (prefixWord ++ tailWord_3550812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550812).length < 2 ^ (prefixWord ++ tailWord_3550812).sum := by decide
  have hdescent : baseEnd_3550812 < baseStart_3550812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550872 : List Nat := [2, 1, 2, 4, 1, 2, 1, 1, 4, 3, 2]
def baseStart_3550872 : Nat := 118140960795 + 3550872 * 2 ^ 59
def prefixEnd_3550872 : Nat := 4983230072969 + 3 ^ 40 * 3550872 * 2
def baseEnd_3550872 : Nat := 1823304078591936430669843

theorem tailTrace_3550872 : CollatzResearch.WordTrace tailWord_3550872 prefixEnd_3550872 1823304078591936430669843 := by
  unfold tailWord_3550872
  simp only [CollatzResearch.WordTrace]
  refine ⟨64755470795902329750751435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86340627727869773001001913 64755470795902329750751435)
  ·
    refine ⟨97133206193853494626127153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64755470795902329750751435 97133206193853494626127153)
    ·
      refine ⟨72849904645390120969595365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97133206193853494626127153 72849904645390120969595365)
      ·
        refine ⟨13659357121010647681799131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72849904645390120969595365 13659357121010647681799131)
        ·
          refine ⟨20489035681515971522698697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13659357121010647681799131 20489035681515971522698697)
          ·
            refine ⟨15366776761136978642024023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20489035681515971522698697 15366776761136978642024023)
            ·
              refine ⟨23050165141705467963036035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15366776761136978642024023 23050165141705467963036035)
              ·
                refine ⟨34575247712558201944554053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23050165141705467963036035 34575247712558201944554053)
                ·
                  refine ⟨6482858946104662864603885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34575247712558201944554053 6482858946104662864603885)
                  ·
                    refine ⟨2431072104789248574226457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6482858946104662864603885 2431072104789248574226457)
                    ·
                      refine ⟨1823304078591936430669843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2431072104789248574226457 1823304078591936430669843)
                      ·
                        rfl

theorem cell23_3550872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_3550872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3550872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3550872 prefixEnd_3550872 := by exact prefixLift 3550872
  have htrace : WordTrace (prefixWord ++ tailWord_3550872) baseStart_3550872 baseEnd_3550872 := by
    simpa [prefixWord, tailWord_3550872, baseEnd_3550872] using wordTrace_append hprefix tailTrace_3550872
  have hstable : (prefixWord ++ tailWord_3550872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550872).length < 2 ^ (prefixWord ++ tailWord_3550872).sum := by decide
  have hdescent : baseEnd_3550872 < baseStart_3550872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550928 : List Nat := [2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 6]
def baseStart_3550928 : Nat := 118140960795 + 3550928 * 2 ^ 59
def prefixEnd_3550928 : Nat := 4983230072969 + 3 ^ 40 * 3550928 * 2
def baseEnd_3550928 : Nat := 1823332833508588211569585

theorem tailTrace_3550928 : CollatzResearch.WordTrace tailWord_3550928 prefixEnd_3550928 1823332833508588211569585 := by
  unfold tailWord_3550928
  simp only [CollatzResearch.WordTrace]
  refine ⟨64756492039800890532770719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86341989386401187377027625 64756492039800890532770719)
  ·
    refine ⟨97134738059701335799156079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64756492039800890532770719 97134738059701335799156079)
    ·
      refine ⟨145702107089552003698734119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97134738059701335799156079 145702107089552003698734119)
      ·
        refine ⟨218553160634328005548101179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145702107089552003698734119 218553160634328005548101179)
        ·
          refine ⟨327829740951492008322151769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218553160634328005548101179 327829740951492008322151769)
          ·
            refine ⟨245872305713619006241613827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 327829740951492008322151769 245872305713619006241613827)
            ·
              refine ⟨368808458570428509362420741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245872305713619006241613827 368808458570428509362420741)
              ·
                refine ⟨69151585981955345505453889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 368808458570428509362420741 69151585981955345505453889)
                ·
                  refine ⟨51863689486466509129090417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69151585981955345505453889 51863689486466509129090417)
                  ·
                    refine ⟨38897767114849881846817813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51863689486466509129090417 38897767114849881846817813)
                    ·
                      refine ⟨1823332833508588211569585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38897767114849881846817813 1823332833508588211569585)
                      ·
                        rfl

theorem cell23_3550928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 6].length) (baseStart_3550928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3550928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3550928 prefixEnd_3550928 := by exact prefixLift 3550928
  have htrace : WordTrace (prefixWord ++ tailWord_3550928) baseStart_3550928 baseEnd_3550928 := by
    simpa [prefixWord, tailWord_3550928, baseEnd_3550928] using wordTrace_append hprefix tailTrace_3550928
  have hstable : (prefixWord ++ tailWord_3550928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550928).length < 2 ^ (prefixWord ++ tailWord_3550928).sum := by decide
  have hdescent : baseEnd_3550928 < baseStart_3550928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550935 : List Nat := [1, 1, 3, 2, 1, 3, 1, 2, 3, 3, 3]
def baseStart_3550935 : Nat := 118140960795 + 3550935 * 2 ^ 59
def prefixEnd_3550935 : Nat := 4983230072969 + 3 ^ 40 * 3550935 * 2
def baseEnd_3550935 : Nat := 1823336427873169684182053

theorem tailTrace_3550935 : CollatzResearch.WordTrace tailWord_3550935 prefixEnd_3550935 1823336427873169684182053 := by
  unfold tailWord_3550935
  simp only [CollatzResearch.WordTrace]
  refine ⟨129513239390576421261046259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86342159593717614174030839 129513239390576421261046259)
  ·
    refine ⟨194269859085864631891569389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129513239390576421261046259 194269859085864631891569389)
    ·
      refine ⟨72851197157199236959338521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194269859085864631891569389 72851197157199236959338521)
      ·
        refine ⟨54638397867899427719503891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72851197157199236959338521 54638397867899427719503891)
        ·
          refine ⟨81957596801849141579255837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54638397867899427719503891 81957596801849141579255837)
          ·
            refine ⟨30734098800693428092220939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81957596801849141579255837 30734098800693428092220939)
            ·
              refine ⟨46101148201040142138331409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30734098800693428092220939 46101148201040142138331409)
              ·
                refine ⟨34575861150780106603748557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46101148201040142138331409 34575861150780106603748557)
                ·
                  refine ⟨12965947931542539976405709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34575861150780106603748557 12965947931542539976405709)
                  ·
                    refine ⟨4862230474328452491152141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12965947931542539976405709 4862230474328452491152141)
                    ·
                      refine ⟨1823336427873169684182053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4862230474328452491152141 1823336427873169684182053)
                      ·
                        rfl

theorem cell23_3550935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 3, 3, 3].length) (baseStart_3550935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3550935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3550935 prefixEnd_3550935 := by exact prefixLift 3550935
  have htrace : WordTrace (prefixWord ++ tailWord_3550935) baseStart_3550935 baseEnd_3550935 := by
    simpa [prefixWord, tailWord_3550935, baseEnd_3550935] using wordTrace_append hprefix tailTrace_3550935
  have hstable : (prefixWord ++ tailWord_3550935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550935).length < 2 ^ (prefixWord ++ tailWord_3550935).sum := by decide
  have hdescent : baseEnd_3550935 < baseStart_3550935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550936 : List Nat := [2, 1, 2, 2, 3, 1, 3, 4, 1, 2, 2]
def baseStart_3550936 : Nat := 118140960795 + 3550936 * 2 ^ 59
def prefixEnd_3550936 : Nat := 4983230072969 + 3 ^ 40 * 3550936 * 2
def baseEnd_3550936 : Nat := 1823336941353824180269549

theorem tailTrace_3550936 : CollatzResearch.WordTrace tailWord_3550936 prefixEnd_3550936 1823336941353824180269549 := by
  unfold tailWord_3550936
  simp only [CollatzResearch.WordTrace]
  refine ⟨64756637931786399215916331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86342183909048532287888441 64756637931786399215916331)
  ·
    refine ⟨97134956897679598823874497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64756637931786399215916331 97134956897679598823874497)
    ·
      refine ⟨72851217673259699117905873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97134956897679598823874497 72851217673259699117905873)
      ·
        refine ⟨54638413254944774338429405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72851217673259699117905873 54638413254944774338429405)
        ·
          refine ⟨20489404970604290376911027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54638413254944774338429405 20489404970604290376911027)
          ·
            refine ⟨30734107455906435565366541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20489404970604290376911027 30734107455906435565366541)
            ·
              refine ⟨11525290295964913337012453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30734107455906435565366541 11525290295964913337012453)
              ·
                refine ⟨2160991930493421250689835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11525290295964913337012453 2160991930493421250689835)
                ·
                  refine ⟨3241487895740131876034753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2160991930493421250689835 3241487895740131876034753)
                  ·
                    refine ⟨2431115921805098907026065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3241487895740131876034753 2431115921805098907026065)
                    ·
                      refine ⟨1823336941353824180269549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2431115921805098907026065 1823336941353824180269549)
                      ·
                        rfl

theorem cell23_3550936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 4, 1, 2, 2].length) (baseStart_3550936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3550936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3550936 prefixEnd_3550936 := by exact prefixLift 3550936
  have htrace : WordTrace (prefixWord ++ tailWord_3550936) baseStart_3550936 baseEnd_3550936 := by
    simpa [prefixWord, tailWord_3550936, baseEnd_3550936] using wordTrace_append hprefix tailTrace_3550936
  have hstable : (prefixWord ++ tailWord_3550936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550936).length < 2 ^ (prefixWord ++ tailWord_3550936).sum := by decide
  have hdescent : baseEnd_3550936 < baseStart_3550936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550952 : List Nat := [2, 1, 4, 1, 3, 1, 1, 3, 1, 3, 3]
def baseStart_3550952 : Nat := 118140960795 + 3550952 * 2 ^ 59
def prefixEnd_3550952 : Nat := 4983230072969 + 3 ^ 40 * 3550952 * 2
def baseEnd_3550952 : Nat := 1823345157044296117669475

theorem tailTrace_3550952 : CollatzResearch.WordTrace tailWord_3550952 prefixEnd_3550952 1823345157044296117669475 := by
  unfold tailWord_3550952
  simp only [CollatzResearch.WordTrace]
  refine ⟨64756929715757416582207555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86342572954343222109610073 64756929715757416582207555)
  ·
    refine ⟨97135394573636124873311333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64756929715757416582207555 97135394573636124873311333)
    ·
      refine ⟨18212886482556773413745875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97135394573636124873311333 18212886482556773413745875)
      ·
        refine ⟨27319329723835160120618813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18212886482556773413745875 27319329723835160120618813)
        ·
          refine ⟨10244748646438185045232055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27319329723835160120618813 10244748646438185045232055)
          ·
            refine ⟨15367122969657277567848083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10244748646438185045232055 15367122969657277567848083)
            ·
              refine ⟨23050684454485916351772125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15367122969657277567848083 23050684454485916351772125)
              ·
                refine ⟨8644006670432218631914547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23050684454485916351772125 8644006670432218631914547)
                ·
                  refine ⟨12966010005648327947871821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8644006670432218631914547 12966010005648327947871821)
                  ·
                    refine ⟨4862253752118122980451933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12966010005648327947871821 4862253752118122980451933)
                    ·
                      refine ⟨1823345157044296117669475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4862253752118122980451933 1823345157044296117669475)
                      ·
                        rfl

theorem cell23_3550952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_3550952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3550952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3550952 prefixEnd_3550952 := by exact prefixLift 3550952
  have htrace : WordTrace (prefixWord ++ tailWord_3550952) baseStart_3550952 baseEnd_3550952 := by
    simpa [prefixWord, tailWord_3550952, baseEnd_3550952] using wordTrace_append hprefix tailTrace_3550952
  have hstable : (prefixWord ++ tailWord_3550952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550952).length < 2 ^ (prefixWord ++ tailWord_3550952).sum := by decide
  have hdescent : baseEnd_3550952 < baseStart_3550952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550986 : List Nat := [3, 1, 2, 2, 1, 5, 1, 2, 2, 1, 3]
def baseStart_3550986 : Nat := 118140960795 + 3550986 * 2 ^ 59
def prefixEnd_3550986 : Nat := 4983230072969 + 3 ^ 40 * 3550986 * 2
def baseEnd_3550986 : Nat := 1823362615386548984644319

theorem tailTrace_3550986 : CollatzResearch.WordTrace tailWord_3550986 prefixEnd_3550986 1823362615386548984644319 := by
  unfold tailWord_3550986
  simp only [CollatzResearch.WordTrace]
  refine ⟨32378774878347914242788203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86343399675594437980768541 32378774878347914242788203)
  ·
    refine ⟨48568162317521871364182305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32378774878347914242788203 48568162317521871364182305)
    ·
      refine ⟨36426121738141403523136729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48568162317521871364182305 36426121738141403523136729)
      ·
        refine ⟨27319591303606052642352547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36426121738141403523136729 27319591303606052642352547)
        ·
          refine ⟨40979386955409078963528821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27319591303606052642352547 40979386955409078963528821)
          ·
            refine ⟨3841817527069601152830827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40979386955409078963528821 3841817527069601152830827)
            ·
              refine ⟨5762726290604401729246241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3841817527069601152830827 5762726290604401729246241)
              ·
                refine ⟨4322044717953301296934681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5762726290604401729246241 4322044717953301296934681)
                ·
                  refine ⟨3241533538464975972701011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4322044717953301296934681 3241533538464975972701011)
                  ·
                    refine ⟨4862300307697463959051517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3241533538464975972701011 4862300307697463959051517)
                    ·
                      refine ⟨1823362615386548984644319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4862300307697463959051517 1823362615386548984644319)
                      ·
                        rfl

theorem cell23_3550986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 2, 2, 1, 3].length) (baseStart_3550986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3550986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3550986 prefixEnd_3550986 := by exact prefixLift 3550986
  have htrace : WordTrace (prefixWord ++ tailWord_3550986) baseStart_3550986 baseEnd_3550986 := by
    simpa [prefixWord, tailWord_3550986, baseEnd_3550986] using wordTrace_append hprefix tailTrace_3550986
  have hstable : (prefixWord ++ tailWord_3550986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550986).length < 2 ^ (prefixWord ++ tailWord_3550986).sum := by decide
  have hdescent : baseEnd_3550986 < baseStart_3550986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3550995 : List Nat := [1, 1, 1, 2, 1, 3, 2, 3, 2, 4, 3]
def baseStart_3550995 : Nat := 118140960795 + 3550995 * 2 ^ 59
def prefixEnd_3550995 : Nat := 4983230072969 + 3 ^ 40 * 3550995 * 2
def baseEnd_3550995 : Nat := 1823367236712439449431777

theorem tailTrace_3550995 : CollatzResearch.WordTrace tailWord_3550995 prefixEnd_3550995 1823367236712439449431777 := by
  unfold tailWord_3550995
  simp only [CollatzResearch.WordTrace]
  refine ⟨129515427770359051508230439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86343618513572701005486959 129515427770359051508230439)
  ·
    refine ⟨194273141655538577262345659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129515427770359051508230439 194273141655538577262345659)
    ·
      refine ⟨291409712483307865893518489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194273141655538577262345659 291409712483307865893518489)
      ·
        refine ⟨218557284362480899420138867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291409712483307865893518489 218557284362480899420138867)
        ·
          refine ⟨327835926543721349130208301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218557284362480899420138867 327835926543721349130208301)
          ·
            refine ⟨122938472453895505923828113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 327835926543721349130208301 122938472453895505923828113)
            ·
              refine ⟨92203854340421629442871085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122938472453895505923828113 92203854340421629442871085)
              ·
                refine ⟨34576445377658111041076657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92203854340421629442871085 34576445377658111041076657)
                ·
                  refine ⟨25932334033243583280807493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34576445377658111041076657 25932334033243583280807493)
                  ·
                    refine ⟨4862312631233171865151405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25932334033243583280807493 4862312631233171865151405)
                    ·
                      refine ⟨1823367236712439449431777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4862312631233171865151405 1823367236712439449431777)
                      ·
                        rfl

theorem cell23_3550995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 4, 3].length) (baseStart_3550995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3550995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3550995 prefixEnd_3550995 := by exact prefixLift 3550995
  have htrace : WordTrace (prefixWord ++ tailWord_3550995) baseStart_3550995 baseEnd_3550995 := by
    simpa [prefixWord, tailWord_3550995, baseEnd_3550995] using wordTrace_append hprefix tailTrace_3550995
  have hstable : (prefixWord ++ tailWord_3550995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3550995).length < 2 ^ (prefixWord ++ tailWord_3550995).sum := by decide
  have hdescent : baseEnd_3550995 < baseStart_3550995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3550995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551009 : List Nat := [1, 2, 3, 2, 1, 3, 3, 1, 1, 4, 2]
def baseStart_3551009 : Nat := 118140960795 + 3551009 * 2 ^ 59
def prefixEnd_3551009 : Nat := 4983230072969 + 3 ^ 40 * 3551009 * 2
def baseEnd_3551009 : Nat := 1823374425441602394656713

theorem tailTrace_3551009 : CollatzResearch.WordTrace tailWord_3551009 prefixEnd_3551009 1823374425441602394656713 := by
  unfold tailWord_3551009
  simp only [CollatzResearch.WordTrace]
  refine ⟨129515938392308331899240081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86343958928205554599493387 129515938392308331899240081)
  ·
    refine ⟨97136953794231248924430061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129515938392308331899240081 97136953794231248924430061)
    ·
      refine ⟨36426357672836718346661273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97136953794231248924430061 36426357672836718346661273)
      ·
        refine ⟨27319768254627538759995955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36426357672836718346661273 27319768254627538759995955)
        ·
          refine ⟨40979652381941308139993933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27319768254627538759995955 40979652381941308139993933)
          ·
            refine ⟨15367369643227990552497725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40979652381941308139993933 15367369643227990552497725)
            ·
              refine ⟨5762763616210496457186647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15367369643227990552497725 5762763616210496457186647)
              ·
                refine ⟨8644145424315744685779971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5762763616210496457186647 8644145424315744685779971)
                ·
                  refine ⟨12966218136473617028669957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8644145424315744685779971 12966218136473617028669957)
                  ·
                    refine ⟨2431165900588803192875617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12966218136473617028669957 2431165900588803192875617)
                    ·
                      refine ⟨1823374425441602394656713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2431165900588803192875617 1823374425441602394656713)
                      ·
                        rfl

theorem cell23_3551009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 1, 1, 4, 2].length) (baseStart_3551009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3551009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3551009 prefixEnd_3551009 := by exact prefixLift 3551009
  have htrace : WordTrace (prefixWord ++ tailWord_3551009) baseStart_3551009 baseEnd_3551009 := by
    simpa [prefixWord, tailWord_3551009, baseEnd_3551009] using wordTrace_append hprefix tailTrace_3551009
  have hstable : (prefixWord ++ tailWord_3551009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551009).length < 2 ^ (prefixWord ++ tailWord_3551009).sum := by decide
  have hdescent : baseEnd_3551009 < baseStart_3551009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551049 : List Nat := [1, 2, 1, 1, 2, 4, 5, 2, 5]
def baseStart_3551049 : Nat := 118140960795 + 3551049 * 2 ^ 59
def prefixEnd_3551049 : Nat := 4983230072969 + 3 ^ 40 * 3551049 * 2
def baseEnd_3551049 : Nat := 202599440518642470906281

theorem tailTrace_3551049 : CollatzResearch.WordTrace tailWord_3551049 prefixEnd_3551049 202599440518642470906281 := by
  unfold tailWord_3551049
  simp only [CollatzResearch.WordTrace]
  refine ⟨129517397312163418730696201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86344931541442279153797467 129517397312163418730696201)
  ·
    refine ⟨97138047984122564048022151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129517397312163418730696201 97138047984122564048022151)
    ·
      refine ⟨145707071976183846072033227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97138047984122564048022151 145707071976183846072033227)
      ·
        refine ⟨218560607964275769108049841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145707071976183846072033227 218560607964275769108049841)
        ·
          refine ⟨163920455973206826831037381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218560607964275769108049841 163920455973206826831037381)
          ·
            refine ⟨30735085494976280030819509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 163920455973206826831037381 30735085494976280030819509)
            ·
              refine ⟨2881414265154026252889329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30735085494976280030819509 2881414265154026252889329)
              ·
                refine ⟨2161060698865519689666997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2881414265154026252889329 2161060698865519689666997)
                ·
                  refine ⟨202599440518642470906281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2161060698865519689666997 202599440518642470906281)
                  ·
                    rfl

theorem cell23_3551049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 2, 5].length) (baseStart_3551049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3551049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3551049 prefixEnd_3551049 := by exact prefixLift 3551049
  have htrace : WordTrace (prefixWord ++ tailWord_3551049) baseStart_3551049 baseEnd_3551049 := by
    simpa [prefixWord, tailWord_3551049, baseEnd_3551049] using wordTrace_append hprefix tailTrace_3551049
  have hstable : (prefixWord ++ tailWord_3551049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551049).length < 2 ^ (prefixWord ++ tailWord_3551049).sum := by decide
  have hdescent : baseEnd_3551049 < baseStart_3551049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551060 : List Nat := [2, 4, 1, 1, 3, 3, 2, 1, 2, 2, 2]
def baseStart_3551060 : Nat := 118140960795 + 3551060 * 2 ^ 59
def prefixEnd_3551060 : Nat := 4983230072969 + 3 ^ 40 * 3551060 * 2
def baseEnd_3551060 : Nat := 1823400612954981695118979

theorem tailTrace_3551060 : CollatzResearch.WordTrace tailWord_3551060 prefixEnd_3551060 1823400612954981695118979 := by
  unfold tailWord_3551060
  simp only [CollatzResearch.WordTrace]
  refine ⟨64758899257561783804673317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86345199010082378406231089 64758899257561783804673317)
  ·
    refine ⟨12142293610792834463376247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64758899257561783804673317 12142293610792834463376247)
    ·
      refine ⟨18213440416189251695064371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12142293610792834463376247 18213440416189251695064371)
      ·
        refine ⟨27320160624283877542596557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18213440416189251695064371 27320160624283877542596557)
        ·
          refine ⟨10245060234106454078473709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27320160624283877542596557 10245060234106454078473709)
          ·
            refine ⟨3841897587789920279427641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10245060234106454078473709 3841897587789920279427641)
            ·
              refine ⟨2881423190842440209570731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3841897587789920279427641 2881423190842440209570731)
              ·
                refine ⟨4322134786263660314356097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2881423190842440209570731 4322134786263660314356097)
                ·
                  refine ⟨3241601089697745235767073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4322134786263660314356097 3241601089697745235767073)
                  ·
                    refine ⟨2431200817273308926825305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3241601089697745235767073 2431200817273308926825305)
                    ·
                      refine ⟨1823400612954981695118979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2431200817273308926825305 1823400612954981695118979)
                      ·
                        rfl

theorem cell23_3551060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2, 1, 2, 2, 2].length) (baseStart_3551060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3551060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3551060 prefixEnd_3551060 := by exact prefixLift 3551060
  have htrace : WordTrace (prefixWord ++ tailWord_3551060) baseStart_3551060 baseEnd_3551060 := by
    simpa [prefixWord, tailWord_3551060, baseEnd_3551060] using wordTrace_append hprefix tailTrace_3551060
  have hstable : (prefixWord ++ tailWord_3551060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551060).length < 2 ^ (prefixWord ++ tailWord_3551060).sum := by decide
  have hdescent : baseEnd_3551060 < baseStart_3551060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551143 : List Nat := [1, 1, 6, 1, 2, 2, 2, 3, 1, 4]
def baseStart_3551143 : Nat := 118140960795 + 3551143 * 2 ^ 59
def prefixEnd_3551143 : Nat := 4983230072969 + 3 ^ 40 * 3551143 * 2
def baseEnd_3551143 : Nat := 607814410616434956793699

theorem tailTrace_3551143 : CollatzResearch.WordTrace tailWord_3551143 prefixEnd_3551143 607814410616434956793699 := by
  unfold tailWord_3551143
  simp only [CollatzResearch.WordTrace]
  refine ⟨129520825773822872784618083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86347217182548581856412055 129520825773822872784618083)
  ·
    refine ⟨194281238660734309176927125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129520825773822872784618083 194281238660734309176927125)
    ·
      refine ⟨9106933062221920742668459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 194281238660734309176927125 9106933062221920742668459)
      ·
        refine ⟨13660399593332881114002689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9106933062221920742668459 13660399593332881114002689)
        ·
          refine ⟨10245299694999660835502017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13660399593332881114002689 10245299694999660835502017)
          ·
            refine ⟨7683974771249745626626513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10245299694999660835502017 7683974771249745626626513)
            ·
              refine ⟨5762981078437309219969885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7683974771249745626626513 5762981078437309219969885)
              ·
                refine ⟨2161117904413990957488707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5762981078437309219969885 2161117904413990957488707)
                ·
                  refine ⟨3241676856620986436233061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2161117904413990957488707 3241676856620986436233061)
                  ·
                    refine ⟨607814410616434956793699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3241676856620986436233061 607814410616434956793699)
                    ·
                      rfl

theorem cell23_3551143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_3551143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3551143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3551143 prefixEnd_3551143 := by exact prefixLift 3551143
  have htrace : WordTrace (prefixWord ++ tailWord_3551143) baseStart_3551143 baseEnd_3551143 := by
    simpa [prefixWord, tailWord_3551143, baseEnd_3551143] using wordTrace_append hprefix tailTrace_3551143
  have hstable : (prefixWord ++ tailWord_3551143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551143).length < 2 ^ (prefixWord ++ tailWord_3551143).sum := by decide
  have hdescent : baseEnd_3551143 < baseStart_3551143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551156 : List Nat := [2, 5, 2, 1, 2, 1, 1, 1, 8]
def baseStart_3551156 : Nat := 118140960795 + 3551156 * 2 ^ 59
def prefixEnd_3551156 : Nat := 4983230072969 + 3 ^ 40 * 3551156 * 2
def baseEnd_3551156 : Nat := 202605545233090368835393

theorem tailTrace_3551156 : CollatzResearch.WordTrace tailWord_3551156 prefixEnd_3551156 202605545233090368835393 := by
  unfold tailWord_3551156
  simp only [CollatzResearch.WordTrace]
  refine ⟨64760649961387888002420661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86347533281850517336560881 64760649961387888002420661)
  ·
    refine ⟨6071310933880114500226937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64760649961387888002420661 6071310933880114500226937)
    ·
      refine ⟨4553483200410085875170203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6071310933880114500226937 4553483200410085875170203)
      ·
        refine ⟨6830224800615128812755305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4553483200410085875170203 6830224800615128812755305)
        ·
          refine ⟨5122668600461346609566479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6830224800615128812755305 5122668600461346609566479)
          ·
            refine ⟨7684002900692019914349719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5122668600461346609566479 7684002900692019914349719)
            ·
              refine ⟨11526004351038029871524579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7684002900692019914349719 11526004351038029871524579)
              ·
                refine ⟨17289006526557044807286869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11526004351038029871524579 17289006526557044807286869)
                ·
                  refine ⟨202605545233090368835393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17289006526557044807286869 202605545233090368835393)
                  ·
                    rfl

theorem cell23_3551156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_3551156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3551156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3551156 prefixEnd_3551156 := by exact prefixLift 3551156
  have htrace : WordTrace (prefixWord ++ tailWord_3551156) baseStart_3551156 baseEnd_3551156 := by
    simpa [prefixWord, tailWord_3551156, baseEnd_3551156] using wordTrace_append hprefix tailTrace_3551156
  have hstable : (prefixWord ++ tailWord_3551156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551156).length < 2 ^ (prefixWord ++ tailWord_3551156).sum := by decide
  have hdescent : baseEnd_3551156 < baseStart_3551156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551159 : List Nat := [1, 1, 3, 1, 3, 1, 1, 3, 4, 3, 2]
def baseStart_3551159 : Nat := 118140960795 + 3551159 * 2 ^ 59
def prefixEnd_3551159 : Nat := 4983230072969 + 3 ^ 40 * 3551159 * 2
def baseEnd_3551159 : Nat := 1823451447539776807781023

theorem tailTrace_3551159 : CollatzResearch.WordTrace tailWord_3551159 prefixEnd_3551159 1823451447539776807781023 := by
  unfold tailWord_3551159
  simp only [CollatzResearch.WordTrace]
  refine ⟨129521409341764907517200531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86347606227843271678133687 129521409341764907517200531)
  ·
    refine ⟨194282114012647361275800797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129521409341764907517200531 194282114012647361275800797)
    ·
      refine ⟨72855792754742760478425299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194282114012647361275800797 72855792754742760478425299)
      ·
        refine ⟨109283689132114140717637949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72855792754742760478425299 109283689132114140717637949)
        ·
          refine ⟨40981383424542802769114231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109283689132114140717637949 40981383424542802769114231)
          ·
            refine ⟨61472075136814204153671347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40981383424542802769114231 61472075136814204153671347)
            ·
              refine ⟨92208112705221306230507021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61472075136814204153671347 92208112705221306230507021)
              ·
                refine ⟨34578042264457989836440133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92208112705221306230507021 34578042264457989836440133)
                ·
                  refine ⟨6483382924585873094332525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34578042264457989836440133 6483382924585873094332525)
                  ·
                    refine ⟨2431268596719702410374697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6483382924585873094332525 2431268596719702410374697)
                    ·
                      refine ⟨1823451447539776807781023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2431268596719702410374697 1823451447539776807781023)
                      ·
                        rfl

theorem cell23_3551159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 4, 3, 2].length) (baseStart_3551159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3551159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3551159 prefixEnd_3551159 := by exact prefixLift 3551159
  have htrace : WordTrace (prefixWord ++ tailWord_3551159) baseStart_3551159 baseEnd_3551159 := by
    simpa [prefixWord, tailWord_3551159, baseEnd_3551159] using wordTrace_append hprefix tailTrace_3551159
  have hstable : (prefixWord ++ tailWord_3551159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551159).length < 2 ^ (prefixWord ++ tailWord_3551159).sum := by decide
  have hdescent : baseEnd_3551159 < baseStart_3551159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551166 : List Nat := [4, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3]
def baseStart_3551166 : Nat := 118140960795 + 3551166 * 2 ^ 59
def prefixEnd_3551166 : Nat := 4983230072969 + 3 ^ 40 * 3551166 * 2
def baseEnd_3551166 : Nat := 1823455041904358280393491

theorem tailTrace_3551166 : CollatzResearch.WordTrace tailWord_3551166 prefixEnd_3551166 1823455041904358280393491 := by
  unfold tailWord_3551166
  simp only [CollatzResearch.WordTrace]
  refine ⟨16190208081592443464088169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86347776435159698475136901 16190208081592443464088169)
  ·
    refine ⟨12142656061194332598066127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16190208081592443464088169 12142656061194332598066127)
    ·
      refine ⟨18213984091791498897099191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12142656061194332598066127 18213984091791498897099191)
      ·
        refine ⟨27320976137687248345648787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18213984091791498897099191 27320976137687248345648787)
        ·
          refine ⟨40981464206530872518473181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27320976137687248345648787 40981464206530872518473181)
          ·
            refine ⟨15368049077449077194427443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40981464206530872518473181 15368049077449077194427443)
            ·
              refine ⟨23052073616173615791641165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15368049077449077194427443 23052073616173615791641165)
              ·
                refine ⟨8644527606065105921865437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23052073616173615791641165 8644527606065105921865437)
                ·
                  refine ⟨3241697852274414720699539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8644527606065105921865437 3241697852274414720699539)
                  ·
                    refine ⟨4862546778411622081049309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3241697852274414720699539 4862546778411622081049309)
                    ·
                      refine ⟨1823455041904358280393491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4862546778411622081049309 1823455041904358280393491)
                      ·
                        rfl

theorem cell23_3551166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3].length) (baseStart_3551166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3551166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3551166 prefixEnd_3551166 := by exact prefixLift 3551166
  have htrace : WordTrace (prefixWord ++ tailWord_3551166) baseStart_3551166 baseEnd_3551166 := by
    simpa [prefixWord, tailWord_3551166, baseEnd_3551166] using wordTrace_append hprefix tailTrace_3551166
  have hstable : (prefixWord ++ tailWord_3551166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551166).length < 2 ^ (prefixWord ++ tailWord_3551166).sum := by decide
  have hdescent : baseEnd_3551166 < baseStart_3551166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551192 : List Nat := [2, 1, 2, 2, 2, 2, 1, 2, 3, 1, 5]
def baseStart_3551192 : Nat := 118140960795 + 3551192 * 2 ^ 59
def prefixEnd_3551192 : Nat := 4983230072969 + 3 ^ 40 * 3551192 * 2
def baseEnd_3551192 : Nat := 1823468392401375178668371

theorem tailTrace_3551192 : CollatzResearch.WordTrace tailWord_3551192 prefixEnd_3551192 1823468392401375178668371 := by
  unfold tailWord_3551192
  simp only [CollatzResearch.WordTrace]
  refine ⟨64761306475322677076575915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86348408633763569435434553 64761306475322677076575915)
  ·
    refine ⟨97141959712984015614863873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64761306475322677076575915 97141959712984015614863873)
    ·
      refine ⟨72856469784738011711147905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97141959712984015614863873 72856469784738011711147905)
      ·
        refine ⟨54642352338553508783360929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72856469784738011711147905 54642352338553508783360929)
        ·
          refine ⟨40981764253915131587520697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54642352338553508783360929 40981764253915131587520697)
          ·
            refine ⟨30736323190436348690640523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40981764253915131587520697 30736323190436348690640523)
            ·
              refine ⟨46104484785654523035960785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30736323190436348690640523 46104484785654523035960785)
              ·
                refine ⟨34578363589240892276970589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46104484785654523035960785 34578363589240892276970589)
                ·
                  refine ⟨12966886345965334603863971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34578363589240892276970589 12966886345965334603863971)
                  ·
                    refine ⟨19450329518948001905795957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12966886345965334603863971 19450329518948001905795957)
                    ·
                      refine ⟨1823468392401375178668371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19450329518948001905795957 1823468392401375178668371)
                      ·
                        rfl

theorem cell23_3551192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_3551192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3551192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3551192 prefixEnd_3551192 := by exact prefixLift 3551192
  have htrace : WordTrace (prefixWord ++ tailWord_3551192) baseStart_3551192 baseEnd_3551192 := by
    simpa [prefixWord, tailWord_3551192, baseEnd_3551192] using wordTrace_append hprefix tailTrace_3551192
  have hstable : (prefixWord ++ tailWord_3551192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551192).length < 2 ^ (prefixWord ++ tailWord_3551192).sum := by decide
  have hdescent : baseEnd_3551192 < baseStart_3551192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551199 : List Nat := [1, 1, 2, 3, 4, 1, 1, 2, 4, 4]
def baseStart_3551199 : Nat := 118140960795 + 3551199 * 2 ^ 59
def prefixEnd_3551199 : Nat := 4983230072969 + 3 ^ 40 * 3551199 * 2
def baseEnd_3551199 : Nat := 607823995588652217093613

theorem tailTrace_3551199 : CollatzResearch.WordTrace tailWord_3551199 prefixEnd_3551199 607823995588652217093613 := by
  unfold tailWord_3551199
  simp only [CollatzResearch.WordTrace]
  refine ⟨129522868261619994348656651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86348578841079996232437767 129522868261619994348656651)
  ·
    refine ⟨194284302392429991522984977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129522868261619994348656651 194284302392429991522984977)
    ·
      refine ⟨145713226794322493642238733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194284302392429991522984977 145713226794322493642238733)
      ·
        refine ⟨54642460047870935115839525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145713226794322493642238733 54642460047870935115839525)
        ·
          refine ⟨10245461258975800334219911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54642460047870935115839525 10245461258975800334219911)
          ·
            refine ⟨15368191888463700501329867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10245461258975800334219911 15368191888463700501329867)
            ·
              refine ⟨23052287832695550751994801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15368191888463700501329867 23052287832695550751994801)
              ·
                refine ⟨17289215874521663063996101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23052287832695550751994801 17289215874521663063996101)
                ·
                  refine ⟨3241727976472811824499269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17289215874521663063996101 3241727976472811824499269)
                  ·
                    refine ⟨607823995588652217093613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3241727976472811824499269 607823995588652217093613)
                    ·
                      rfl

theorem cell23_3551199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 4, 4].length) (baseStart_3551199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3551199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3551199 prefixEnd_3551199 := by exact prefixLift 3551199
  have htrace : WordTrace (prefixWord ++ tailWord_3551199) baseStart_3551199 baseEnd_3551199 := by
    simpa [prefixWord, tailWord_3551199, baseEnd_3551199] using wordTrace_append hprefix tailTrace_3551199
  have hstable : (prefixWord ++ tailWord_3551199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551199).length < 2 ^ (prefixWord ++ tailWord_3551199).sum := by decide
  have hdescent : baseEnd_3551199 < baseStart_3551199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551274 : List Nat := [3, 1, 4, 1, 2, 3, 2, 2, 1, 2, 2]
def baseStart_3551274 : Nat := 118140960795 + 3551274 * 2 ^ 59
def prefixEnd_3551274 : Nat := 4983230072969 + 3 ^ 40 * 3551274 * 2
def baseEnd_3551274 : Nat := 1823510497815043857842995

theorem tailTrace_3551274 : CollatzResearch.WordTrace tailWord_3551274 prefixEnd_3551274 1823510497815043857842995 := by
  unfold tailWord_3551274
  simp only [CollatzResearch.WordTrace]
  refine ⟨32381400934087070539409219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86350402490898854771757917 32381400934087070539409219)
  ·
    refine ⟨48572101401130605809113829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32381400934087070539409219 48572101401130605809113829)
    ·
      refine ⟨9107269012711988589208843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48572101401130605809113829 9107269012711988589208843)
      ·
        refine ⟨13660903519067982883813265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9107269012711988589208843 13660903519067982883813265)
        ·
          refine ⟨10245677639300987162859949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13660903519067982883813265 10245677639300987162859949)
          ·
            refine ⟨3842129114737870186072481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10245677639300987162859949 3842129114737870186072481)
            ·
              refine ⟨2881596836053402639554361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3842129114737870186072481 2881596836053402639554361)
              ·
                refine ⟨2161197627040051979665771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2881596836053402639554361 2161197627040051979665771)
                ·
                  refine ⟨3241796440560077969498657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2161197627040051979665771 3241796440560077969498657)
                  ·
                    refine ⟨2431347330420058477123993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3241796440560077969498657 2431347330420058477123993)
                    ·
                      refine ⟨1823510497815043857842995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2431347330420058477123993 1823510497815043857842995)
                      ·
                        rfl

theorem cell23_3551274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_3551274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3551274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3551274 prefixEnd_3551274 := by exact prefixLift 3551274
  have htrace : WordTrace (prefixWord ++ tailWord_3551274) baseStart_3551274 baseEnd_3551274 := by
    simpa [prefixWord, tailWord_3551274, baseEnd_3551274] using wordTrace_append hprefix tailTrace_3551274
  have hstable : (prefixWord ++ tailWord_3551274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551274).length < 2 ^ (prefixWord ++ tailWord_3551274).sum := by decide
  have hdescent : baseEnd_3551274 < baseStart_3551274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551296 : List Nat := [2, 1, 1, 2, 2, 4, 1, 3, 1, 4, 2]
def baseStart_3551296 : Nat := 118140960795 + 3551296 * 2 ^ 59
def prefixEnd_3551296 : Nat := 4983230072969 + 3 ^ 40 * 3551296 * 2
def baseEnd_3551296 : Nat := 1823521794389442771767893

theorem tailTrace_3551296 : CollatzResearch.WordTrace tailWord_3551296 prefixEnd_3551296 1823521794389442771767893 := by
  unfold tailWord_3551296
  simp only [CollatzResearch.WordTrace]
  refine ⟨64763203071134289957468871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86350937428179053276625161 64763203071134289957468871)
  ·
    refine ⟨97144804606701434936203307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64763203071134289957468871 97144804606701434936203307)
    ·
      refine ⟨145717206910052152404304961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97144804606701434936203307 145717206910052152404304961)
      ·
        refine ⟨109287905182539114303228721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145717206910052152404304961 109287905182539114303228721)
        ·
          refine ⟨81965928886904335727421541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109287905182539114303228721 81965928886904335727421541)
          ·
            refine ⟨15368611666294562948891539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81965928886904335727421541 15368611666294562948891539)
            ·
              refine ⟨23052917499441844423337309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15368611666294562948891539 23052917499441844423337309)
              ·
                refine ⟨8644844062290691658751491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23052917499441844423337309 8644844062290691658751491)
                ·
                  refine ⟨12967266093436037488127237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8644844062290691658751491 12967266093436037488127237)
                  ·
                    refine ⟨2431362392519257029023857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12967266093436037488127237 2431362392519257029023857)
                    ·
                      refine ⟨1823521794389442771767893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2431362392519257029023857 1823521794389442771767893)
                      ·
                        rfl

theorem cell23_3551296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 3, 1, 4, 2].length) (baseStart_3551296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3551296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3551296 prefixEnd_3551296 := by exact prefixLift 3551296
  have htrace : WordTrace (prefixWord ++ tailWord_3551296) baseStart_3551296 baseEnd_3551296 := by
    simpa [prefixWord, tailWord_3551296, baseEnd_3551296] using wordTrace_append hprefix tailTrace_3551296
  have hstable : (prefixWord ++ tailWord_3551296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551296).length < 2 ^ (prefixWord ++ tailWord_3551296).sum := by decide
  have hdescent : baseEnd_3551296 < baseStart_3551296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551312 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 7]
def baseStart_3551312 : Nat := 118140960795 + 3551312 * 2 ^ 59
def prefixEnd_3551312 : Nat := 4983230072969 + 3 ^ 40 * 3551312 * 2
def baseEnd_3551312 : Nat := 1823530010079914709167819

theorem tailTrace_3551312 : CollatzResearch.WordTrace tailWord_3551312 prefixEnd_3551312 1823530010079914709167819 := by
  unfold tailWord_3551312
  simp only [CollatzResearch.WordTrace]
  refine ⟨64763494855105307323760095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86351326473473743098346793 64763494855105307323760095)
  ·
    refine ⟨97145242282657960985640143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64763494855105307323760095 97145242282657960985640143)
    ·
      refine ⟨145717863423986941478460215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97145242282657960985640143 145717863423986941478460215)
      ·
        refine ⟨218576795135980412217690323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145717863423986941478460215 218576795135980412217690323)
        ·
          refine ⟨327865192703970618326535485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218576795135980412217690323 327865192703970618326535485)
          ·
            refine ⟨122949447263988981872450807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 327865192703970618326535485 122949447263988981872450807)
            ·
              refine ⟨184424170895983472808676211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122949447263988981872450807 184424170895983472808676211)
              ·
                refine ⟨276636256343975209213014317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184424170895983472808676211 276636256343975209213014317)
                ·
                  refine ⟨103738596128990703454880369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 276636256343975209213014317 103738596128990703454880369)
                  ·
                    refine ⟨77803947096743027591160277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 103738596128990703454880369 77803947096743027591160277)
                    ·
                      refine ⟨1823530010079914709167819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 77803947096743027591160277 1823530010079914709167819)
                      ·
                        rfl

theorem cell23_3551312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 7].length) (baseStart_3551312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3551312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3551312 prefixEnd_3551312 := by exact prefixLift 3551312
  have htrace : WordTrace (prefixWord ++ tailWord_3551312) baseStart_3551312 baseEnd_3551312 := by
    simpa [prefixWord, tailWord_3551312, baseEnd_3551312] using wordTrace_append hprefix tailTrace_3551312
  have hstable : (prefixWord ++ tailWord_3551312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551312).length < 2 ^ (prefixWord ++ tailWord_3551312).sum := by decide
  have hdescent : baseEnd_3551312 < baseStart_3551312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551346 : List Nat := [3, 2, 1, 2, 2, 2, 2, 1, 2, 3, 3]
def baseStart_3551346 : Nat := 118140960795 + 3551346 * 2 ^ 59
def prefixEnd_3551346 : Nat := 4983230072969 + 3 ^ 40 * 3551346 * 2
def baseEnd_3551346 : Nat := 1823547468422167576142663

theorem tailTrace_3551346 : CollatzResearch.WordTrace tailWord_3551346 prefixEnd_3551346 1823547468422167576142663 := by
  unfold tailWord_3551346
  simp only [CollatzResearch.WordTrace]
  refine ⟨32382057448021859613564473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86352153194724958969505261 32382057448021859613564473)
  ·
    refine ⟨24286543086016394710173355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32382057448021859613564473 24286543086016394710173355)
    ·
      refine ⟨36429814629024592065260033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24286543086016394710173355 36429814629024592065260033)
      ·
        refine ⟨27322360971768444048945025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36429814629024592065260033 27322360971768444048945025)
        ·
          refine ⟨20491770728826333036708769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27322360971768444048945025 20491770728826333036708769)
          ·
            refine ⟨15368828046619749777531577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20491770728826333036708769 15368828046619749777531577)
            ·
              refine ⟨11526621034964812333148683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15368828046619749777531577 11526621034964812333148683)
              ·
                refine ⟨17289931552447218499723025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11526621034964812333148683 17289931552447218499723025)
                ·
                  refine ⟨12967448664335413874792269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17289931552447218499723025 12967448664335413874792269)
                  ·
                    refine ⟨4862793249125780203047101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12967448664335413874792269 4862793249125780203047101)
                    ·
                      refine ⟨1823547468422167576142663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4862793249125780203047101 1823547468422167576142663)
                      ·
                        rfl

theorem cell23_3551346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_3551346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3551346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3551346 prefixEnd_3551346 := by exact prefixLift 3551346
  have htrace : WordTrace (prefixWord ++ tailWord_3551346) baseStart_3551346 baseEnd_3551346 := by
    simpa [prefixWord, tailWord_3551346, baseEnd_3551346] using wordTrace_append hprefix tailTrace_3551346
  have hstable : (prefixWord ++ tailWord_3551346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551346).length < 2 ^ (prefixWord ++ tailWord_3551346).sum := by decide
  have hdescent : baseEnd_3551346 < baseStart_3551346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551369 : List Nat := [1, 2, 1, 1, 4, 2, 1, 3, 1, 3, 4]
def baseStart_3551369 : Nat := 118140960795 + 3551369 * 2 ^ 59
def prefixEnd_3551369 : Nat := 4983230072969 + 3 ^ 40 * 3551369 * 2
def baseEnd_3551369 : Nat := 1823559278477220986155057

theorem tailTrace_3551369 : CollatzResearch.WordTrace tailWord_3551369 prefixEnd_3551369 1823559278477220986155057 := by
  unfold tailWord_3551369
  simp only [CollatzResearch.WordTrace]
  refine ⟨129529068671004113382345161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86352712447336075588230107 129529068671004113382345161)
  ·
    refine ⟨97146801503253085036758871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129529068671004113382345161 97146801503253085036758871)
    ·
      refine ⟨145720202254879627555138307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97146801503253085036758871 145720202254879627555138307)
      ·
        refine ⟨218580303382319441332707461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145720202254879627555138307 218580303382319441332707461)
        ·
          refine ⟨40983806884184895249882649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 218580303382319441332707461 40983806884184895249882649)
          ·
            refine ⟨30737855163138671437411987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40983806884184895249882649 30737855163138671437411987)
            ·
              refine ⟨46106782744708007156117981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30737855163138671437411987 46106782744708007156117981)
              ·
                refine ⟨17290043529265502683544243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46106782744708007156117981 17290043529265502683544243)
                ·
                  refine ⟨25935065293898254025316365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17290043529265502683544243 25935065293898254025316365)
                  ·
                    refine ⟨9725649485211845259493637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25935065293898254025316365 9725649485211845259493637)
                    ·
                      refine ⟨1823559278477220986155057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9725649485211845259493637 1823559278477220986155057)
                      ·
                        rfl

theorem cell23_3551369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 3, 4].length) (baseStart_3551369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3551369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3551369 prefixEnd_3551369 := by exact prefixLift 3551369
  have htrace : WordTrace (prefixWord ++ tailWord_3551369) baseStart_3551369 baseEnd_3551369 := by
    simpa [prefixWord, tailWord_3551369, baseEnd_3551369] using wordTrace_append hprefix tailTrace_3551369
  have hstable : (prefixWord ++ tailWord_3551369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551369).length < 2 ^ (prefixWord ++ tailWord_3551369).sum := by decide
  have hdescent : baseEnd_3551369 < baseStart_3551369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551479 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 2, 5, 5]
def baseStart_3551479 : Nat := 118140960795 + 3551479 * 2 ^ 59
def prefixEnd_3551479 : Nat := 4983230072969 + 3 ^ 40 * 3551479 * 2
def baseEnd_3551479 : Nat := 1823615761349215555779551

theorem tailTrace_3551479 : CollatzResearch.WordTrace tailWord_3551479 prefixEnd_3551479 1823615761349215555779551 := by
  unfold tailWord_3551479
  simp only [CollatzResearch.WordTrace]
  refine ⟨129533080700605602168849491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86355387133737068112566327 129533080700605602168849491)
  ·
    refine ⟨194299621050908403253274237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129533080700605602168849491 194299621050908403253274237)
    ·
      refine ⟨72862357894090651219977839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194299621050908403253274237 72862357894090651219977839)
      ·
        refine ⟨109293536841135976829966759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72862357894090651219977839 109293536841135976829966759)
        ·
          refine ⟨163940305261703965244950139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109293536841135976829966759 163940305261703965244950139)
          ·
            refine ⟨245910457892555947867425209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163940305261703965244950139 245910457892555947867425209)
            ·
              refine ⟨184432843419416960900568907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 245910457892555947867425209 184432843419416960900568907)
              ·
                refine ⟨276649265129125441350853361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184432843419416960900568907 276649265129125441350853361)
                ·
                  refine ⟨207486948846844081013140021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 276649265129125441350853361 207486948846844081013140021)
                  ·
                    refine ⟨19451901454391632594981877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 207486948846844081013140021 19451901454391632594981877)
                    ·
                      refine ⟨1823615761349215555779551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19451901454391632594981877 1823615761349215555779551)
                      ·
                        rfl

theorem cell23_3551479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5, 5].length) (baseStart_3551479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3551479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3551479 prefixEnd_3551479 := by exact prefixLift 3551479
  have htrace : WordTrace (prefixWord ++ tailWord_3551479) baseStart_3551479 baseEnd_3551479 := by
    simpa [prefixWord, tailWord_3551479, baseEnd_3551479] using wordTrace_append hprefix tailTrace_3551479
  have hstable : (prefixWord ++ tailWord_3551479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551479).length < 2 ^ (prefixWord ++ tailWord_3551479).sum := by decide
  have hdescent : baseEnd_3551479 < baseStart_3551479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551490 : List Nat := [3, 4, 1, 1, 2, 2, 1, 3, 1, 5]
def baseStart_3551490 : Nat := 118140960795 + 3551490 * 2 ^ 59
def prefixEnd_3551490 : Nat := 4983230072969 + 3 ^ 40 * 3551490 * 2
def baseEnd_3551490 : Nat := 607873803212138337580667

theorem tailTrace_3551490 : CollatzResearch.WordTrace tailWord_3551490 prefixEnd_3551490 607873803212138337580667 := by
  unfold tailWord_3551490
  simp only [CollatzResearch.WordTrace]
  refine ⟨32383370475891437761874981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86355654602377167364999949 32383370475891437761874981)
  ·
    refine ⟨6071881964229644580351559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32383370475891437761874981 6071881964229644580351559)
    ·
      refine ⟨9107822946344466870527339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6071881964229644580351559 9107822946344466870527339)
      ·
        refine ⟨13661734419516700305791009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9107822946344466870527339 13661734419516700305791009)
        ·
          refine ⟨10246300814637525229343257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13661734419516700305791009 10246300814637525229343257)
          ·
            refine ⟨7684725610978143922007443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10246300814637525229343257 7684725610978143922007443)
            ·
              refine ⟨11527088416467215883011165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7684725610978143922007443 11527088416467215883011165)
              ·
                refine ⟨4322658156175205956129187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11527088416467215883011165 4322658156175205956129187)
                ·
                  refine ⟨6483987234262808934193781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4322658156175205956129187 6483987234262808934193781)
                  ·
                    refine ⟨607873803212138337580667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6483987234262808934193781 607873803212138337580667)
                    ·
                      rfl

theorem cell23_3551490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_3551490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3551490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3551490 prefixEnd_3551490 := by exact prefixLift 3551490
  have htrace : WordTrace (prefixWord ++ tailWord_3551490) baseStart_3551490 baseEnd_3551490 := by
    simpa [prefixWord, tailWord_3551490, baseEnd_3551490] using wordTrace_append hprefix tailTrace_3551490
  have hstable : (prefixWord ++ tailWord_3551490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551490).length < 2 ^ (prefixWord ++ tailWord_3551490).sum := by decide
  have hdescent : baseEnd_3551490 < baseStart_3551490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551499 : List Nat := [1, 1, 1, 1, 5, 2, 12]
def baseStart_3551499 : Nat := 118140960795 + 3551499 * 2 ^ 59
def prefixEnd_3551499 : Nat := 4983230072969 + 3 ^ 40 * 3551499 * 2
def baseEnd_3551499 : Nat := 22513901616818586142339

theorem tailTrace_3551499 : CollatzResearch.WordTrace tailWord_3551499 prefixEnd_3551499 22513901616818586142339 := by
  unfold tailWord_3551499
  simp only [CollatzResearch.WordTrace]
  refine ⟨129533810160533145584577551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86355873440355430389718367 129533810160533145584577551)
  ·
    refine ⟨194300715240799718376866327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129533810160533145584577551 194300715240799718376866327)
    ·
      refine ⟨291451072861199577565299491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194300715240799718376866327 291451072861199577565299491)
      ·
        refine ⟨437176609291799366347949237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291451072861199577565299491 437176609291799366347949237)
        ·
          refine ⟨40985307121106190595120241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 437176609291799366347949237 40985307121106190595120241)
          ·
            refine ⟨30738980340829642946340181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40985307121106190595120241 30738980340829642946340181)
            ·
              refine ⟨22513901616818586142339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 30738980340829642946340181 22513901616818586142339)
              ·
                rfl

theorem cell23_3551499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 12].length) (baseStart_3551499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3551499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3551499 prefixEnd_3551499 := by exact prefixLift 3551499
  have htrace : WordTrace (prefixWord ++ tailWord_3551499) baseStart_3551499 baseEnd_3551499 := by
    simpa [prefixWord, tailWord_3551499, baseEnd_3551499] using wordTrace_append hprefix tailTrace_3551499
  have hstable : (prefixWord ++ tailWord_3551499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551499).length < 2 ^ (prefixWord ++ tailWord_3551499).sum := by decide
  have hdescent : baseEnd_3551499 < baseStart_3551499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551600 : List Nat := [2, 1, 1, 1, 4, 4, 1, 2, 1, 4, 2]
def baseStart_3551600 : Nat := 118140960795 + 3551600 * 2 ^ 59
def prefixEnd_3551600 : Nat := 4983230072969 + 3 ^ 40 * 3551600 * 2
def baseEnd_3551600 : Nat := 1823677892508409582366495

theorem tailTrace_3551600 : CollatzResearch.WordTrace tailWord_3551600 prefixEnd_3551600 1823677892508409582366495 := by
  unfold tailWord_3551600
  simp only [CollatzResearch.WordTrace]
  refine ⟨64768746966583619917002127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86358329288778159889336169 64768746966583619917002127)
  ·
    refine ⟨97153120449875429875503191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64768746966583619917002127 97153120449875429875503191)
    ·
      refine ⟨145729680674813144813254787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97153120449875429875503191 145729680674813144813254787)
      ·
        refine ⟨218594521012219717219882181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145729680674813144813254787 218594521012219717219882181)
        ·
          refine ⟨40986472689791196978727909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 218594521012219717219882181 40986472689791196978727909)
          ·
            refine ⟨7684963629335849433511483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40986472689791196978727909 7684963629335849433511483)
            ·
              refine ⟨11527445444003774150267225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7684963629335849433511483 11527445444003774150267225)
              ·
                refine ⟨8645584083002830612700419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11527445444003774150267225 8645584083002830612700419)
                ·
                  refine ⟨12968376124504245919050629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8645584083002830612700419 12968376124504245919050629)
                  ·
                    refine ⟨2431570523344546109821993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12968376124504245919050629 2431570523344546109821993)
                    ·
                      refine ⟨1823677892508409582366495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2431570523344546109821993 1823677892508409582366495)
                      ·
                        rfl

theorem cell23_3551600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 2, 1, 4, 2].length) (baseStart_3551600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3551600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3551600 prefixEnd_3551600 := by exact prefixLift 3551600
  have htrace : WordTrace (prefixWord ++ tailWord_3551600) baseStart_3551600 baseEnd_3551600 := by
    simpa [prefixWord, tailWord_3551600, baseEnd_3551600] using wordTrace_append hprefix tailTrace_3551600
  have hstable : (prefixWord ++ tailWord_3551600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551600).length < 2 ^ (prefixWord ++ tailWord_3551600).sum := by decide
  have hdescent : baseEnd_3551600 < baseStart_3551600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551630 : List Nat := [4, 1, 1, 4, 1, 2, 1, 1, 2, 2, 4]
def baseStart_3551630 : Nat := 118140960795 + 3551630 * 2 ^ 59
def prefixEnd_3551630 : Nat := 4983230072969 + 3 ^ 40 * 3551630 * 2
def baseEnd_3551630 : Nat := 1823693296928044464991357

theorem tailTrace_3551630 : CollatzResearch.WordTrace tailWord_3551630 prefixEnd_3551630 1823693296928044464991357 := by
  unfold tailWord_3551630
  simp only [CollatzResearch.WordTrace]
  refine ⟨16192323515382319369699543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86359058748705703305064229 16192323515382319369699543)
  ·
    refine ⟨24288485273073479054549315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16192323515382319369699543 24288485273073479054549315)
    ·
      refine ⟨36432727909610218581823973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24288485273073479054549315 36432727909610218581823973)
      ·
        refine ⟨6831136483051915984091995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36432727909610218581823973 6831136483051915984091995)
        ·
          refine ⟨10246704724577873976137993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6831136483051915984091995 10246704724577873976137993)
          ·
            refine ⟨7685028543433405482103495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10246704724577873976137993 7685028543433405482103495)
            ·
              refine ⟨11527542815150108223155243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7685028543433405482103495 11527542815150108223155243)
              ·
                refine ⟨17291314222725162334732865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11527542815150108223155243 17291314222725162334732865)
                ·
                  refine ⟨12968485667043871751049649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17291314222725162334732865 12968485667043871751049649)
                  ·
                    refine ⟨9726364250282903813287237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12968485667043871751049649 9726364250282903813287237)
                    ·
                      refine ⟨1823693296928044464991357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9726364250282903813287237 1823693296928044464991357)
                      ·
                        rfl

theorem cell23_3551630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_3551630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3551630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3551630 prefixEnd_3551630 := by exact prefixLift 3551630
  have htrace : WordTrace (prefixWord ++ tailWord_3551630) baseStart_3551630 baseEnd_3551630 := by
    simpa [prefixWord, tailWord_3551630, baseEnd_3551630] using wordTrace_append hprefix tailTrace_3551630
  have hstable : (prefixWord ++ tailWord_3551630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551630).length < 2 ^ (prefixWord ++ tailWord_3551630).sum := by decide
  have hdescent : baseEnd_3551630 < baseStart_3551630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551690 : List Nat := [3, 1, 2, 1, 2, 2, 1, 3, 2, 4, 2]
def baseStart_3551690 : Nat := 118140960795 + 3551690 * 2 ^ 59
def prefixEnd_3551690 : Nat := 4983230072969 + 3 ^ 40 * 3551690 * 2
def baseEnd_3551690 : Nat := 1823724105767314230241081

theorem tailTrace_3551690 : CollatzResearch.WordTrace tailWord_3551690 prefixEnd_3551690 1823724105767314230241081 := by
  unfold tailWord_3551690
  simp only [CollatzResearch.WordTrace]
  refine ⟨32385194125710296301195131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86360517668560790136520349 32385194125710296301195131)
  ·
    refine ⟨48577791188565444451792697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32385194125710296301195131 48577791188565444451792697)
    ·
      refine ⟨36433343391424083338844523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48577791188565444451792697 36433343391424083338844523)
      ·
        refine ⟨54650015087136125008266785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36433343391424083338844523 54650015087136125008266785)
        ·
          refine ⟨40987511315352093756200089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54650015087136125008266785 40987511315352093756200089)
          ·
            refine ⟨30740633486514070317150067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40987511315352093756200089 30740633486514070317150067)
            ·
              refine ⟨46110950229771105475725101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30740633486514070317150067 46110950229771105475725101)
              ·
                refine ⟨17291606336164164553396913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46110950229771105475725101 17291606336164164553396913)
                ·
                  refine ⟨12968704752123123415047685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17291606336164164553396913 12968704752123123415047685)
                  ·
                    refine ⟨2431632141023085640321441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12968704752123123415047685 2431632141023085640321441)
                    ·
                      refine ⟨1823724105767314230241081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2431632141023085640321441 1823724105767314230241081)
                      ·
                        rfl

theorem cell23_3551690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 2, 4, 2].length) (baseStart_3551690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3551690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3551690 prefixEnd_3551690 := by exact prefixLift 3551690
  have htrace : WordTrace (prefixWord ++ tailWord_3551690) baseStart_3551690 baseEnd_3551690 := by
    simpa [prefixWord, tailWord_3551690, baseEnd_3551690] using wordTrace_append hprefix tailTrace_3551690
  have hstable : (prefixWord ++ tailWord_3551690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551690).length < 2 ^ (prefixWord ++ tailWord_3551690).sum := by decide
  have hdescent : baseEnd_3551690 < baseStart_3551690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551696 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 12]
def baseStart_3551696 : Nat := 118140960795 + 3551696 * 2 ^ 59
def prefixEnd_3551696 : Nat := 4983230072969 + 3 ^ 40 * 3551696 * 2
def baseEnd_3551696 : Nat := 202636354072360134085117

theorem tailTrace_3551696 : CollatzResearch.WordTrace tailWord_3551696 prefixEnd_3551696 202636354072360134085117 := by
  unfold tailWord_3551696
  simp only [CollatzResearch.WordTrace]
  refine ⟨64770497670409724114749471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86360663560546298819665961 64770497670409724114749471)
  ·
    refine ⟨97155746505614586172124207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64770497670409724114749471 97155746505614586172124207)
    ·
      refine ⟨145733619758421879258186311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97155746505614586172124207 145733619758421879258186311)
      ·
        refine ⟨218600429637632818887279467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145733619758421879258186311 218600429637632818887279467)
        ·
          refine ⟨327900644456449228330919201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218600429637632818887279467 327900644456449228330919201)
          ·
            refine ⟨245925483342336921248189401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 327900644456449228330919201 245925483342336921248189401)
            ·
              refine ⟨184444112506752690936142051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 245925483342336921248189401 184444112506752690936142051)
              ·
                refine ⟨276666168760129036404213077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184444112506752690936142051 276666168760129036404213077)
                ·
                  refine ⟨202636354072360134085117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 276666168760129036404213077 202636354072360134085117)
                  ·
                    rfl

theorem cell23_3551696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 12].length) (baseStart_3551696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3551696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3551696 prefixEnd_3551696 := by exact prefixLift 3551696
  have htrace : WordTrace (prefixWord ++ tailWord_3551696) baseStart_3551696 baseEnd_3551696 := by
    simpa [prefixWord, tailWord_3551696, baseEnd_3551696] using wordTrace_append hprefix tailTrace_3551696
  have hstable : (prefixWord ++ tailWord_3551696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551696).length < 2 ^ (prefixWord ++ tailWord_3551696).sum := by decide
  have hdescent : baseEnd_3551696 < baseStart_3551696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551743 : List Nat := [1, 1, 2, 2, 1, 2, 4, 2, 3, 5]
def baseStart_3551743 : Nat := 118140960795 + 3551743 * 2 ^ 59
def prefixEnd_3551743 : Nat := 4983230072969 + 3 ^ 40 * 3551743 * 2
def baseEnd_3551743 : Nat := 607917106747334174292779

theorem tailTrace_3551743 : CollatzResearch.WordTrace tailWord_3551743 prefixEnd_3551743 607917106747334174292779 := by
  unfold tailWord_3551743
  simp only [CollatzResearch.WordTrace]
  refine ⟨129542709571649175256459883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86361806381099450170973255 129542709571649175256459883)
  ·
    refine ⟨194314064357473762884689825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129542709571649175256459883 194314064357473762884689825)
    ·
      refine ⟨145735548268105322163517369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194314064357473762884689825 145735548268105322163517369)
      ·
        refine ⟨109301661201078991622638027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145735548268105322163517369 109301661201078991622638027)
        ·
          refine ⟨163952491801618487433957041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109301661201078991622638027 163952491801618487433957041)
          ·
            refine ⟨122964368851213865575467781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163952491801618487433957041 122964368851213865575467781)
            ·
              refine ⟨23055819159602599795400209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122964368851213865575467781 23055819159602599795400209)
              ·
                refine ⟨17291864369701949846550157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23055819159602599795400209 17291864369701949846550157)
                ·
                  refine ⟨6484449138638231192456309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17291864369701949846550157 6484449138638231192456309)
                  ·
                    refine ⟨607917106747334174292779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6484449138638231192456309 607917106747334174292779)
                    ·
                      rfl

theorem cell23_3551743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 3, 5].length) (baseStart_3551743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3551743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3551743 prefixEnd_3551743 := by exact prefixLift 3551743
  have htrace : WordTrace (prefixWord ++ tailWord_3551743) baseStart_3551743 baseEnd_3551743 := by
    simpa [prefixWord, tailWord_3551743, baseEnd_3551743] using wordTrace_append hprefix tailTrace_3551743
  have hstable : (prefixWord ++ tailWord_3551743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551743).length < 2 ^ (prefixWord ++ tailWord_3551743).sum := by decide
  have hdescent : baseEnd_3551743 < baseStart_3551743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551777 : List Nat := [1, 2, 3, 2, 2, 1, 5, 1, 1, 5]
def baseStart_3551777 : Nat := 118140960795 + 3551777 * 2 ^ 59
def prefixEnd_3551777 : Nat := 4983230072969 + 3 ^ 40 * 3551777 * 2
def baseEnd_3551777 : Nat := 607922926194751796617727

theorem tailTrace_3551777 : CollatzResearch.WordTrace tailWord_3551777 prefixEnd_3551777 607922926194751796617727 := by
  unfold tailWord_3551777
  simp only [CollatzResearch.WordTrace]
  refine ⟨129543949653525999063197585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86362633102350666042131723 129543949653525999063197585)
  ·
    refine ⟨97157962240144499297398189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129543949653525999063197585 97157962240144499297398189)
    ·
      refine ⟨36434235840054187236524321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97157962240144499297398189 36434235840054187236524321)
      ·
        refine ⟨27325676880040640427393241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36434235840054187236524321 27325676880040640427393241)
        ·
          refine ⟨20494257660030480320544931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27325676880040640427393241 20494257660030480320544931)
          ·
            refine ⟨30741386490045720480817397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20494257660030480320544931 30741386490045720480817397)
            ·
              refine ⟨2882004983441786295076631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30741386490045720480817397 2882004983441786295076631)
              ·
                refine ⟨4323007475162679442614947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2882004983441786295076631 4323007475162679442614947)
                ·
                  refine ⟨6484511212744019163922421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4323007475162679442614947 6484511212744019163922421)
                  ·
                    refine ⟨607922926194751796617727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6484511212744019163922421 607922926194751796617727)
                    ·
                      rfl

theorem cell23_3551777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5, 1, 1, 5].length) (baseStart_3551777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3551777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3551777 prefixEnd_3551777 := by exact prefixLift 3551777
  have htrace : WordTrace (prefixWord ++ tailWord_3551777) baseStart_3551777 baseEnd_3551777 := by
    simpa [prefixWord, tailWord_3551777, baseEnd_3551777] using wordTrace_append hprefix tailTrace_3551777
  have hstable : (prefixWord ++ tailWord_3551777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551777).length < 2 ^ (prefixWord ++ tailWord_3551777).sum := by decide
  have hdescent : baseEnd_3551777 < baseStart_3551777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551784 : List Nat := [2, 1, 5, 2, 1, 1, 2, 2, 2, 3, 2]
def baseStart_3551784 : Nat := 118140960795 + 3551784 * 2 ^ 59
def prefixEnd_3551784 : Nat := 4983230072969 + 3 ^ 40 * 3551784 * 2
def baseEnd_3551784 : Nat := 1823772372948836862465649

theorem tailTrace_3551784 : CollatzResearch.WordTrace tailWord_3551784 prefixEnd_3551784 1823772372948836862465649 := by
  unfold tailWord_3551784
  simp only [CollatzResearch.WordTrace]
  refine ⟨64772102482250319629351203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86362803309667092839134937 64772102482250319629351203)
  ·
    refine ⟨97158153723375479444026805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64772102482250319629351203 97158153723375479444026805)
    ·
      refine ⟨9108576911566451197877513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97158153723375479444026805 9108576911566451197877513)
      ·
        refine ⟨6831432683674838398408135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9108576911566451197877513 6831432683674838398408135)
        ·
          refine ⟨10247149025512257597612203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6831432683674838398408135 10247149025512257597612203)
          ·
            refine ⟨15370723538268386396418305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10247149025512257597612203 15370723538268386396418305)
            ·
              refine ⟨11528042653701289797313729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15370723538268386396418305 11528042653701289797313729)
              ·
                refine ⟨8646031990275967347985297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11528042653701289797313729 8646031990275967347985297)
                ·
                  refine ⟨6484523992706975510988973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8646031990275967347985297 6484523992706975510988973)
                  ·
                    refine ⟨2431696497265115816620865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6484523992706975510988973 2431696497265115816620865)
                    ·
                      refine ⟨1823772372948836862465649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2431696497265115816620865 1823772372948836862465649)
                      ·
                        rfl

theorem cell23_3551784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_3551784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3551784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3551784 prefixEnd_3551784 := by exact prefixLift 3551784
  have htrace : WordTrace (prefixWord ++ tailWord_3551784) baseStart_3551784 baseEnd_3551784 := by
    simpa [prefixWord, tailWord_3551784, baseEnd_3551784] using wordTrace_append hprefix tailTrace_3551784
  have hstable : (prefixWord ++ tailWord_3551784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551784).length < 2 ^ (prefixWord ++ tailWord_3551784).sum := by decide
  have hdescent : baseEnd_3551784 < baseStart_3551784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551793 : List Nat := [1, 2, 2, 3, 1, 1, 2, 1, 3, 1, 6]
def baseStart_3551793 : Nat := 118140960795 + 3551793 * 2 ^ 59
def prefixEnd_3551793 : Nat := 4983230072969 + 3 ^ 40 * 3551793 * 2
def baseEnd_3551793 : Nat := 1823776994274727327253107

theorem tailTrace_3551793 : CollatzResearch.WordTrace tailWord_3551793 prefixEnd_3551793 1823776994274727327253107 := by
  unfold tailWord_3551793
  simp only [CollatzResearch.WordTrace]
  refine ⟨129544533221468033795780033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86363022147645355863853355 129544533221468033795780033)
  ·
    refine ⟨97158399916101025346835025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129544533221468033795780033 97158399916101025346835025)
    ·
      refine ⟨72868799937075769010126269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97158399916101025346835025 72868799937075769010126269)
      ·
        refine ⟨27325799976403413378797351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72868799937075769010126269 27325799976403413378797351)
        ·
          refine ⟨40988699964605120068196027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27325799976403413378797351 40988699964605120068196027)
          ·
            refine ⟨61483049946907680102294041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40988699964605120068196027 61483049946907680102294041)
            ·
              refine ⟨46112287460180760076720531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61483049946907680102294041 46112287460180760076720531)
              ·
                refine ⟨69168431190271140115080797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46112287460180760076720531 69168431190271140115080797)
                ·
                  refine ⟨25938161696351677543155299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69168431190271140115080797 25938161696351677543155299)
                  ·
                    refine ⟨38907242544527516314732949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25938161696351677543155299 38907242544527516314732949)
                    ·
                      refine ⟨1823776994274727327253107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38907242544527516314732949 1823776994274727327253107)
                      ·
                        rfl

theorem cell23_3551793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_3551793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3551793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3551793 prefixEnd_3551793 := by exact prefixLift 3551793
  have htrace : WordTrace (prefixWord ++ tailWord_3551793) baseStart_3551793 baseEnd_3551793 := by
    simpa [prefixWord, tailWord_3551793, baseEnd_3551793] using wordTrace_append hprefix tailTrace_3551793
  have hstable : (prefixWord ++ tailWord_3551793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551793).length < 2 ^ (prefixWord ++ tailWord_3551793).sum := by decide
  have hdescent : baseEnd_3551793 < baseStart_3551793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551800 : List Nat := [2, 1, 2, 1, 4, 1, 1, 1, 5, 2, 3]
def baseStart_3551800 : Nat := 118140960795 + 3551800 * 2 ^ 59
def prefixEnd_3551800 : Nat := 4983230072969 + 3 ^ 40 * 3551800 * 2
def baseEnd_3551800 : Nat := 1823780588639308799865575

theorem tailTrace_3551800 : CollatzResearch.WordTrace tailWord_3551800 prefixEnd_3551800 1823780588639308799865575 := by
  unfold tailWord_3551800
  simp only [CollatzResearch.WordTrace]
  refine ⟨64772394266221336995642427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86363192354961782660856569 64772394266221336995642427)
  ·
    refine ⟨97158591399332005493463641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64772394266221336995642427 97158591399332005493463641)
    ·
      refine ⟨72868943549499004120097731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97158591399332005493463641 72868943549499004120097731)
      ·
        refine ⟨109303415324248506180146597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72868943549499004120097731 109303415324248506180146597)
        ·
          refine ⟨20494390373296594908777487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109303415324248506180146597 20494390373296594908777487)
          ·
            refine ⟨30741585559944892363166231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20494390373296594908777487 30741585559944892363166231)
            ·
              refine ⟨46112378339917338544749347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30741585559944892363166231 46112378339917338544749347)
              ·
                refine ⟨69168567509876007817124021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46112378339917338544749347 69168567509876007817124021)
                ·
                  refine ⟨6484553204050875732855377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69168567509876007817124021 6484553204050875732855377)
                  ·
                    refine ⟨4863414903038156799641533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6484553204050875732855377 4863414903038156799641533)
                    ·
                      refine ⟨1823780588639308799865575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4863414903038156799641533 1823780588639308799865575)
                      ·
                        rfl

theorem cell23_3551800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 5, 2, 3].length) (baseStart_3551800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3551800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3551800 prefixEnd_3551800 := by exact prefixLift 3551800
  have htrace : WordTrace (prefixWord ++ tailWord_3551800) baseStart_3551800 baseEnd_3551800 := by
    simpa [prefixWord, tailWord_3551800, baseEnd_3551800] using wordTrace_append hprefix tailTrace_3551800
  have hstable : (prefixWord ++ tailWord_3551800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551800).length < 2 ^ (prefixWord ++ tailWord_3551800).sum := by decide
  have hdescent : baseEnd_3551800 < baseStart_3551800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551814 : List Nat := [6, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4]
def baseStart_3551814 : Nat := 118140960795 + 3551814 * 2 ^ 59
def prefixEnd_3551814 : Nat := 4983230072969 + 3 ^ 40 * 3551814 * 2
def baseEnd_3551814 : Nat := 1823787777368471745090511

theorem tailTrace_3551814 : CollatzResearch.WordTrace tailWord_3551814 prefixEnd_3551814 1823787777368471745090511 := by
  unfold tailWord_3551814
  simp only [CollatzResearch.WordTrace]
  refine ⟨4048290598574748574446703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 86363532769594636254862997 4048290598574748574446703)
  ·
    refine ⟨6072435897862122861670055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4048290598574748574446703 6072435897862122861670055)
    ·
      refine ⟨9108653846793184292505083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6072435897862122861670055 9108653846793184292505083)
      ·
        refine ⟨13662980770189776438757625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9108653846793184292505083 13662980770189776438757625)
        ·
          refine ⟨10247235577642332329068219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13662980770189776438757625 10247235577642332329068219)
          ·
            refine ⟨15370853366463498493602329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10247235577642332329068219 15370853366463498493602329)
            ·
              refine ⟨11528140024847623870201747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15370853366463498493602329 11528140024847623870201747)
              ·
                refine ⟨17292210037271435805302621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11528140024847623870201747 17292210037271435805302621)
                ·
                  refine ⟨6484578763976788426988483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17292210037271435805302621 6484578763976788426988483)
                  ·
                    refine ⟨9726868145965182640482725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6484578763976788426988483 9726868145965182640482725)
                    ·
                      refine ⟨1823787777368471745090511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9726868145965182640482725 1823787777368471745090511)
                      ·
                        rfl

theorem cell23_3551814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_3551814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3551814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3551814 prefixEnd_3551814 := by exact prefixLift 3551814
  have htrace : WordTrace (prefixWord ++ tailWord_3551814) baseStart_3551814 baseEnd_3551814 := by
    simpa [prefixWord, tailWord_3551814, baseEnd_3551814] using wordTrace_append hprefix tailTrace_3551814
  have hstable : (prefixWord ++ tailWord_3551814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551814).length < 2 ^ (prefixWord ++ tailWord_3551814).sum := by decide
  have hdescent : baseEnd_3551814 < baseStart_3551814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551820 : List Nat := [2, 2, 1, 3, 1, 2, 5, 7]
def baseStart_3551820 : Nat := 118140960795 + 3551820 * 2 ^ 59
def prefixEnd_3551820 : Nat := 4983230072969 + 3 ^ 40 * 3551820 * 2
def baseEnd_3551820 : Nat := 67547809564903656356129

theorem tailTrace_3551820 : CollatzResearch.WordTrace tailWord_3551820 prefixEnd_3551820 67547809564903656356129 := by
  unfold tailWord_3551820
  simp only [CollatzResearch.WordTrace]
  refine ⟨64772758996185108703506457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86363678661580144938008609 64772758996185108703506457)
  ·
    refine ⟨48579569247138831527629843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64772758996185108703506457 48579569247138831527629843)
    ·
      refine ⟨72869353870708247291444765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48579569247138831527629843 72869353870708247291444765)
      ·
        refine ⟨27326007701515592734291787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72869353870708247291444765 27326007701515592734291787)
        ·
          refine ⟨40989011552273389101437681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27326007701515592734291787 40989011552273389101437681)
          ·
            refine ⟨30741758664205041826078261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40989011552273389101437681 30741758664205041826078261)
            ·
              refine ⟨2882039874769222671194837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30741758664205041826078261 2882039874769222671194837)
              ·
                refine ⟨67547809564903656356129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2882039874769222671194837 67547809564903656356129)
                ·
                  rfl

theorem cell23_3551820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5, 7].length) (baseStart_3551820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3551820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3551820 prefixEnd_3551820 := by exact prefixLift 3551820
  have htrace : WordTrace (prefixWord ++ tailWord_3551820) baseStart_3551820 baseEnd_3551820 := by
    simpa [prefixWord, tailWord_3551820, baseEnd_3551820] using wordTrace_append hprefix tailTrace_3551820
  have hstable : (prefixWord ++ tailWord_3551820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551820).length < 2 ^ (prefixWord ++ tailWord_3551820).sum := by decide
  have hdescent : baseEnd_3551820 < baseStart_3551820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551831 : List Nat := [1, 1, 3, 2, 2, 2, 4, 3, 1, 2, 2]
def baseStart_3551831 : Nat := 118140960795 + 3551831 * 2 ^ 59
def prefixEnd_3551831 : Nat := 4983230072969 + 3 ^ 40 * 3551831 * 2
def baseEnd_3551831 : Nat := 1823796506539598178577933

theorem tailTrace_3551831 : CollatzResearch.WordTrace tailWord_3551831 prefixEnd_3551831 1823796506539598178577933 := by
  unfold tailWord_3551831
  simp only [CollatzResearch.WordTrace]
  refine ⟨129545919195330366285663347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86363946130220244190442231 129545919195330366285663347)
  ·
    refine ⟨194318878792995549428495021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129545919195330366285663347 194318878792995549428495021)
    ·
      refine ⟨72869579547373331035685633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194318878792995549428495021 72869579547373331035685633)
      ·
        refine ⟨54652184660529998276764225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72869579547373331035685633 54652184660529998276764225)
        ·
          refine ⟨40989138495397498707573169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54652184660529998276764225 40989138495397498707573169)
          ·
            refine ⟨30741853871548124030679877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40989138495397498707573169 30741853871548124030679877)
            ·
              refine ⟨5764097600915273255752477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30741853871548124030679877 5764097600915273255752477)
              ·
                refine ⟨2161536600343227470907179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5764097600915273255752477 2161536600343227470907179)
                ·
                  refine ⟨3242304900514841206360769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2161536600343227470907179 3242304900514841206360769)
                  ·
                    refine ⟨2431728675386130904770577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3242304900514841206360769 2431728675386130904770577)
                    ·
                      refine ⟨1823796506539598178577933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2431728675386130904770577 1823796506539598178577933)
                      ·
                        rfl

theorem cell23_3551831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 3, 1, 2, 2].length) (baseStart_3551831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3551831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3551831 prefixEnd_3551831 := by exact prefixLift 3551831
  have htrace : WordTrace (prefixWord ++ tailWord_3551831) baseStart_3551831 baseEnd_3551831 := by
    simpa [prefixWord, tailWord_3551831, baseEnd_3551831] using wordTrace_append hprefix tailTrace_3551831
  have hstable : (prefixWord ++ tailWord_3551831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551831).length < 2 ^ (prefixWord ++ tailWord_3551831).sum := by decide
  have hdescent : baseEnd_3551831 < baseStart_3551831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551861 : List Nat := [1, 3, 4, 2, 3, 1, 1, 1, 1, 2, 4]
def baseStart_3551861 : Nat := 118140960795 + 3551861 * 2 ^ 59
def prefixEnd_3551861 : Nat := 4983230072969 + 3 ^ 40 * 3551861 * 2
def baseEnd_3551861 : Nat := 1823811910959233061202795

theorem tailTrace_3551861 : CollatzResearch.WordTrace tailWord_3551861 prefixEnd_3551861 1823811910959233061202795 := by
  unfold tailWord_3551861
  simp only [CollatzResearch.WordTrace]
  refine ⟨129547013385221681409255437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86364675590147787606170291 129547013385221681409255437)
  ·
    refine ⟨48580130019458130528470789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129547013385221681409255437 48580130019458130528470789)
    ·
      refine ⟨9108774378648399474088273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48580130019458130528470789 9108774378648399474088273)
      ·
        refine ⟨6831580783986299605566205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9108774378648399474088273 6831580783986299605566205)
        ·
          refine ⟨2561842793994862352087327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6831580783986299605566205 2561842793994862352087327)
          ·
            refine ⟨3842764190992293528130991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2561842793994862352087327 3842764190992293528130991)
            ·
              refine ⟨5764146286488440292196487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3842764190992293528130991 5764146286488440292196487)
              ·
                refine ⟨8646219429732660438294731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5764146286488440292196487 8646219429732660438294731)
                ·
                  refine ⟨12969329144598990657442097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8646219429732660438294731 12969329144598990657442097)
                  ·
                    refine ⟨9726996858449242993081573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12969329144598990657442097 9726996858449242993081573)
                    ·
                      refine ⟨1823811910959233061202795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9726996858449242993081573 1823811910959233061202795)
                      ·
                        rfl

theorem cell23_3551861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_3551861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3551861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3551861 prefixEnd_3551861 := by exact prefixLift 3551861
  have htrace : WordTrace (prefixWord ++ tailWord_3551861) baseStart_3551861 baseEnd_3551861 := by
    simpa [prefixWord, tailWord_3551861, baseEnd_3551861] using wordTrace_append hprefix tailTrace_3551861
  have hstable : (prefixWord ++ tailWord_3551861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551861).length < 2 ^ (prefixWord ++ tailWord_3551861).sum := by decide
  have hdescent : baseEnd_3551861 < baseStart_3551861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551920 : List Nat := [2, 1, 1, 1, 2, 1, 3, 3, 1, 5, 3]
def baseStart_3551920 : Nat := 118140960795 + 3551920 * 2 ^ 59
def prefixEnd_3551920 : Nat := 4983230072969 + 3 ^ 40 * 3551920 * 2
def baseEnd_3551920 : Nat := 1823842206317848330365023

theorem tailTrace_3551920 : CollatzResearch.WordTrace tailWord_3551920 prefixEnd_3551920 1823842206317848330365023 := by
  unfold tailWord_3551920
  simp only [CollatzResearch.WordTrace]
  refine ⟨64774582646003967242826607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86366110194671956323768809 64774582646003967242826607)
  ·
    refine ⟨97161873969005950864239911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64774582646003967242826607 97161873969005950864239911)
    ·
      refine ⟨145742810953508926296359867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97161873969005950864239911 145742810953508926296359867)
      ·
        refine ⟨218614216430263389444539801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145742810953508926296359867 218614216430263389444539801)
        ·
          refine ⟨163960662322697542083404851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218614216430263389444539801 163960662322697542083404851)
          ·
            refine ⟨245940993484046313125107277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163960662322697542083404851 245940993484046313125107277)
            ·
              refine ⟨92227872556517367421915229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 245940993484046313125107277 92227872556517367421915229)
              ·
                refine ⟨34585452208694012783218211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92227872556517367421915229 34585452208694012783218211)
                ·
                  refine ⟨51878178313041019174827317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34585452208694012783218211 51878178313041019174827317)
                  ·
                    refine ⟨4863579216847595547640061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51878178313041019174827317 4863579216847595547640061)
                    ·
                      refine ⟨1823842206317848330365023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4863579216847595547640061 1823842206317848330365023)
                      ·
                        rfl

theorem cell23_3551920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5, 3].length) (baseStart_3551920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3551920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3551920 prefixEnd_3551920 := by exact prefixLift 3551920
  have htrace : WordTrace (prefixWord ++ tailWord_3551920) baseStart_3551920 baseEnd_3551920 := by
    simpa [prefixWord, tailWord_3551920, baseEnd_3551920] using wordTrace_append hprefix tailTrace_3551920
  have hstable : (prefixWord ++ tailWord_3551920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551920).length < 2 ^ (prefixWord ++ tailWord_3551920).sum := by decide
  have hdescent : baseEnd_3551920 < baseStart_3551920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551942 : List Nat := [6, 1, 2, 1, 2, 1, 3, 1, 1, 3, 2]
def baseStart_3551942 : Nat := 118140960795 + 3551942 * 2 ^ 59
def prefixEnd_3551942 : Nat := 4983230072969 + 3 ^ 40 * 3551942 * 2
def baseEnd_3551942 : Nat := 1823853502892247244289923

theorem tailTrace_3551942 : CollatzResearch.WordTrace tailWord_3551942 prefixEnd_3551942 1823853502892247244289923 := by
  unfold tailWord_3551942
  simp only [CollatzResearch.WordTrace]
  refine ⟨4048436490560257257592315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 86366645131952154828636053 4048436490560257257592315)
  ·
    refine ⟨6072654735840385886388473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4048436490560257257592315 6072654735840385886388473)
    ·
      refine ⟨4554491051880289414791355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6072654735840385886388473 4554491051880289414791355)
      ·
        refine ⟨6831736577820434122187033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4554491051880289414791355 6831736577820434122187033)
        ·
          refine ⟨5123802433365325591640275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6831736577820434122187033 5123802433365325591640275)
          ·
            refine ⟨7685703650047988387460413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5123802433365325591640275 7685703650047988387460413)
            ·
              refine ⟨2882138868767995645297655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7685703650047988387460413 2882138868767995645297655)
              ·
                refine ⟨4323208303151993467946483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2882138868767995645297655 4323208303151993467946483)
                ·
                  refine ⟨6484812454727990201919725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4323208303151993467946483 6484812454727990201919725)
                  ·
                    refine ⟨2431804670522996325719897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6484812454727990201919725 2431804670522996325719897)
                    ·
                      refine ⟨1823853502892247244289923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2431804670522996325719897 1823853502892247244289923)
                      ·
                        rfl

theorem cell23_3551942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_3551942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3551942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3551942 prefixEnd_3551942 := by exact prefixLift 3551942
  have htrace : WordTrace (prefixWord ++ tailWord_3551942) baseStart_3551942 baseEnd_3551942 := by
    simpa [prefixWord, tailWord_3551942, baseEnd_3551942] using wordTrace_append hprefix tailTrace_3551942
  have hstable : (prefixWord ++ tailWord_3551942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551942).length < 2 ^ (prefixWord ++ tailWord_3551942).sum := by decide
  have hdescent : baseEnd_3551942 < baseStart_3551942 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551977 : List Nat := [1, 2, 1, 1, 1, 2, 5, 1, 1, 6, 2]
def baseStart_3551977 : Nat := 118140960795 + 3551977 * 2 ^ 59
def prefixEnd_3551977 : Nat := 4983230072969 + 3 ^ 40 * 3551977 * 2
def baseEnd_3551977 : Nat := 1823871474715154607352261

theorem tailTrace_3551977 : CollatzResearch.WordTrace tailWord_3551977 prefixEnd_3551977 1823871474715154607352261 := by
  unfold tailWord_3551977
  simp only [CollatzResearch.WordTrace]
  refine ⟨129551244252801433220478185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86367496168534288813652123 129551244252801433220478185)
  ·
    refine ⟨97163433189601074915358639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129551244252801433220478185 97163433189601074915358639)
    ·
      refine ⟨145745149784401612373037959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97163433189601074915358639 145745149784401612373037959)
      ·
        refine ⟨218617724676602418559556939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145745149784401612373037959 218617724676602418559556939)
        ·
          refine ⟨327926587014903627839335409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218617724676602418559556939 327926587014903627839335409)
          ·
            refine ⟨245944940261177720879501557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 327926587014903627839335409 245944940261177720879501557)
            ·
              refine ⟨23057338149485411332453271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 245944940261177720879501557 23057338149485411332453271)
              ·
                refine ⟨34586007224228116998679907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23057338149485411332453271 34586007224228116998679907)
                ·
                  refine ⟨51879010836342175498019861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34586007224228116998679907 51879010836342175498019861)
                  ·
                    refine ⟨2431828632953539476469681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 51879010836342175498019861 2431828632953539476469681)
                    ·
                      refine ⟨1823871474715154607352261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2431828632953539476469681 1823871474715154607352261)
                      ·
                        rfl

theorem cell23_3551977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 6, 2].length) (baseStart_3551977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3551977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3551977 prefixEnd_3551977 := by exact prefixLift 3551977
  have htrace : WordTrace (prefixWord ++ tailWord_3551977) baseStart_3551977 baseEnd_3551977 := by
    simpa [prefixWord, tailWord_3551977, baseEnd_3551977] using wordTrace_append hprefix tailTrace_3551977
  have hstable : (prefixWord ++ tailWord_3551977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551977).length < 2 ^ (prefixWord ++ tailWord_3551977).sum := by decide
  have hdescent : baseEnd_3551977 < baseStart_3551977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3551997 : List Nat := [1, 4, 1, 1, 1, 1, 5, 1, 1, 4, 3]
def baseStart_3551997 : Nat := 118140960795 + 3551997 * 2 ^ 59
def prefixEnd_3551997 : Nat := 4983230072969 + 3 ^ 40 * 3551997 * 2
def baseEnd_3551997 : Nat := 1823881744328244529102169

theorem tailTrace_3551997 : CollatzResearch.WordTrace tailWord_3551997 prefixEnd_3551997 1823881744328244529102169 := by
  unfold tailWord_3551997
  simp only [CollatzResearch.WordTrace]
  refine ⟨129551973712728976636206245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86367982475152651090804163 129551973712728976636206245)
  ·
    refine ⟨24290995071136683119288671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129551973712728976636206245 24290995071136683119288671)
    ·
      refine ⟨36436492606705024678933007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24290995071136683119288671 36436492606705024678933007)
      ·
        refine ⟨54654738910057537018399511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36436492606705024678933007 54654738910057537018399511)
        ·
          refine ⟨81982108365086305527599267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54654738910057537018399511 81982108365086305527599267)
          ·
            refine ⟨122973162547629458291398901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81982108365086305527599267 122973162547629458291398901)
            ·
              refine ⟨11528733988840261714818647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 122973162547629458291398901 11528733988840261714818647)
              ·
                refine ⟨17293100983260392572227971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11528733988840261714818647 17293100983260392572227971)
                ·
                  refine ⟨25939651474890588858341957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17293100983260392572227971 25939651474890588858341957)
                  ·
                    refine ⟨4863684651541985410939117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25939651474890588858341957 4863684651541985410939117)
                    ·
                      refine ⟨1823881744328244529102169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4863684651541985410939117 1823881744328244529102169)
                      ·
                        rfl

theorem cell23_3551997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 4, 3].length) (baseStart_3551997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3551997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3551997 prefixEnd_3551997 := by exact prefixLift 3551997
  have htrace : WordTrace (prefixWord ++ tailWord_3551997) baseStart_3551997 baseEnd_3551997 := by
    simpa [prefixWord, tailWord_3551997, baseEnd_3551997] using wordTrace_append hprefix tailTrace_3551997
  have hstable : (prefixWord ++ tailWord_3551997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3551997).length < 2 ^ (prefixWord ++ tailWord_3551997).sum := by decide
  have hdescent : baseEnd_3551997 < baseStart_3551997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3551997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552007 : List Nat := [1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 6]
def baseStart_3552007 : Nat := 118140960795 + 3552007 * 2 ^ 59
def prefixEnd_3552007 : Nat := 4983230072969 + 3 ^ 40 * 3552007 * 2
def baseEnd_3552007 : Nat := 1823886879134789489977123

theorem tailTrace_3552007 : CollatzResearch.WordTrace tailWord_3552007 prefixEnd_3552007 1823886879134789489977123 := by
  unfold tailWord_3552007
  simp only [CollatzResearch.WordTrace]
  refine ⟨129552338442692748344070275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86368225628461832229380183 129552338442692748344070275)
  ·
    refine ⟨194328507664039122516105413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129552338442692748344070275 194328507664039122516105413)
    ·
      refine ⟨36436595187007335471769765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194328507664039122516105413 36436595187007335471769765)
      ·
        refine ⟨6831861597563875400956831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36436595187007335471769765 6831861597563875400956831)
        ·
          refine ⟨10247792396345813101435247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6831861597563875400956831 10247792396345813101435247)
          ·
            refine ⟨15371688594518719652152871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10247792396345813101435247 15371688594518719652152871)
            ·
              refine ⟨23057532891778079478229307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15371688594518719652152871 23057532891778079478229307)
              ·
                refine ⟨34586299337667119217343961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23057532891778079478229307 34586299337667119217343961)
                ·
                  refine ⟨25939724503250339413007971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34586299337667119217343961 25939724503250339413007971)
                  ·
                    refine ⟨38909586754875509119511957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25939724503250339413007971 38909586754875509119511957)
                    ·
                      refine ⟨1823886879134789489977123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38909586754875509119511957 1823886879134789489977123)
                      ·
                        rfl

theorem cell23_3552007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_3552007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3552007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3552007 prefixEnd_3552007 := by exact prefixLift 3552007
  have htrace : WordTrace (prefixWord ++ tailWord_3552007) baseStart_3552007 baseEnd_3552007 := by
    simpa [prefixWord, tailWord_3552007, baseEnd_3552007] using wordTrace_append hprefix tailTrace_3552007
  have hstable : (prefixWord ++ tailWord_3552007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552007).length < 2 ^ (prefixWord ++ tailWord_3552007).sum := by decide
  have hdescent : baseEnd_3552007 < baseStart_3552007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552017 : List Nat := [1, 2, 2, 1, 1, 3, 5, 2, 6]
def baseStart_3552017 : Nat := 118140960795 + 3552017 * 2 ^ 59
def prefixEnd_3552017 : Nat := 4983230072969 + 3 ^ 40 * 3552017 * 2
def baseEnd_3552017 : Nat := 202654668215703827872453

theorem tailTrace_3552017 : CollatzResearch.WordTrace tailWord_3552017 prefixEnd_3552017 202654668215703827872453 := by
  unfold tailWord_3552017
  simp only [CollatzResearch.WordTrace]
  refine ⟨129552703172656520051934305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86368468781771013367956203 129552703172656520051934305)
  ·
    refine ⟨97164527379492390038950729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129552703172656520051934305 97164527379492390038950729)
    ·
      refine ⟨72873395534619292529213047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97164527379492390038950729 72873395534619292529213047)
      ·
        refine ⟨109310093301928938793819571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72873395534619292529213047 109310093301928938793819571)
        ·
          refine ⟨163965139952893408190729357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109310093301928938793819571 163965139952893408190729357)
          ·
            refine ⟨61486927482335028071523509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163965139952893408190729357 61486927482335028071523509)
            ·
              refine ⟨5764399451468908881705329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61486927482335028071523509 5764399451468908881705329)
              ·
                refine ⟨4323299588601681661278997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5764399451468908881705329 4323299588601681661278997)
                ·
                  refine ⟨202654668215703827872453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4323299588601681661278997 202654668215703827872453)
                  ·
                    rfl

theorem cell23_3552017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 2, 6].length) (baseStart_3552017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3552017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3552017 prefixEnd_3552017 := by exact prefixLift 3552017
  have htrace : WordTrace (prefixWord ++ tailWord_3552017) baseStart_3552017 baseEnd_3552017 := by
    simpa [prefixWord, tailWord_3552017, baseEnd_3552017] using wordTrace_append hprefix tailTrace_3552017
  have hstable : (prefixWord ++ tailWord_3552017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552017).length < 2 ^ (prefixWord ++ tailWord_3552017).sum := by decide
  have hdescent : baseEnd_3552017 < baseStart_3552017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552044 : List Nat := [2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 3]
def baseStart_3552044 : Nat := 118140960795 + 3552044 * 2 ^ 59
def prefixEnd_3552044 : Nat := 4983230072969 + 3 ^ 40 * 3552044 * 2
def baseEnd_3552044 : Nat := 1823905877919005845214453

theorem tailTrace_3552044 : CollatzResearch.WordTrace tailWord_3552044 prefixEnd_3552044 1823905877919005845214453 := by
  unfold tailWord_3552044
  simp only [CollatzResearch.WordTrace]
  refine ⟨64776843971779351831583593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86369125295705802442111457 64776843971779351831583593)
  ·
    refine ⟨48582632978834513873687695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64776843971779351831583593 48582632978834513873687695)
    ·
      refine ⟨72873949468251770810531543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48582632978834513873687695 72873949468251770810531543)
      ·
        refine ⟨109310924202377656215797315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72873949468251770810531543 109310924202377656215797315)
        ·
          refine ⟨163966386303566484323695973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109310924202377656215797315 163966386303566484323695973)
          ·
            refine ⟨30743697431918715810692995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 163966386303566484323695973 30743697431918715810692995)
            ·
              refine ⟨46115546147878073716039493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30743697431918715810692995 46115546147878073716039493)
              ·
                refine ⟨8646664902727138821757405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46115546147878073716039493 8646664902727138821757405)
                ·
                  refine ⟨3242499338522677058159027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8646664902727138821757405 3242499338522677058159027)
                  ·
                    refine ⟨4863749007784015587238541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3242499338522677058159027 4863749007784015587238541)
                    ·
                      refine ⟨1823905877919005845214453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4863749007784015587238541 1823905877919005845214453)
                      ·
                        rfl

theorem cell23_3552044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 3].length) (baseStart_3552044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3552044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3552044 prefixEnd_3552044 := by exact prefixLift 3552044
  have htrace : WordTrace (prefixWord ++ tailWord_3552044) baseStart_3552044 baseEnd_3552044 := by
    simpa [prefixWord, tailWord_3552044, baseEnd_3552044] using wordTrace_append hprefix tailTrace_3552044
  have hstable : (prefixWord ++ tailWord_3552044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552044).length < 2 ^ (prefixWord ++ tailWord_3552044).sum := by decide
  have hdescent : baseEnd_3552044 < baseStart_3552044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552098 : List Nat := [3, 3, 2, 1, 3, 2, 1, 2, 1, 5]
def baseStart_3552098 : Nat := 118140960795 + 3552098 * 2 ^ 59
def prefixEnd_3552098 : Nat := 4983230072969 + 3 ^ 40 * 3552098 * 2
def baseEnd_3552098 : Nat := 607977868624782877979735

theorem tailTrace_3552098 : CollatzResearch.WordTrace tailWord_3552098 prefixEnd_3552098 607977868624782877979735 := by
  unfold tailWord_3552098
  simp only [CollatzResearch.WordTrace]
  refine ⟨32388914371340767721408237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86370438323575380590421965 32388914371340767721408237)
  ·
    refine ⟨12145842889252787895528089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32388914371340767721408237 12145842889252787895528089)
    ·
      refine ⟨9109382166939590921646067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12145842889252787895528089 9109382166939590921646067)
      ·
        refine ⟨13664073250409386382469101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9109382166939590921646067 13664073250409386382469101)
        ·
          refine ⟨5124027468903519893425913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13664073250409386382469101 5124027468903519893425913)
          ·
            refine ⟨3843020601677639920069435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5124027468903519893425913 3843020601677639920069435)
            ·
              refine ⟨5764530902516459880104153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3843020601677639920069435 5764530902516459880104153)
              ·
                refine ⟨4323398176887344910078115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5764530902516459880104153 4323398176887344910078115)
                ·
                  refine ⟨6485097265331017365117173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4323398176887344910078115 6485097265331017365117173)
                  ·
                    refine ⟨607977868624782877979735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6485097265331017365117173 607977868624782877979735)
                    ·
                      rfl

theorem cell23_3552098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_3552098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3552098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3552098 prefixEnd_3552098 := by exact prefixLift 3552098
  have htrace : WordTrace (prefixWord ++ tailWord_3552098) baseStart_3552098 baseEnd_3552098 := by
    simpa [prefixWord, tailWord_3552098, baseEnd_3552098] using wordTrace_append hprefix tailTrace_3552098
  have hstable : (prefixWord ++ tailWord_3552098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552098).length < 2 ^ (prefixWord ++ tailWord_3552098).sum := by decide
  have hdescent : baseEnd_3552098 < baseStart_3552098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552101 : List Nat := [1, 3, 1, 3, 1, 1, 2, 4, 3, 2, 2]
def baseStart_3552101 : Nat := 118140960795 + 3552101 * 2 ^ 59
def prefixEnd_3552101 : Nat := 4983230072969 + 3 ^ 40 * 3552101 * 2
def baseEnd_3552101 : Nat := 1823935146316312122201691

theorem tailTrace_3552101 : CollatzResearch.WordTrace tailWord_3552101 prefixEnd_3552101 1823935146316312122201691 := by
  unfold tailWord_3552101
  simp only [CollatzResearch.WordTrace]
  refine ⟨129555766904352202397992157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86370511269568134931994771 129555766904352202397992157)
  ·
    refine ⟨48583412589132075899247059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129555766904352202397992157 48583412589132075899247059)
    ·
      refine ⟨72875118883698113848870589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48583412589132075899247059 72875118883698113848870589)
      ·
        refine ⟨27328169581386792693326471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72875118883698113848870589 27328169581386792693326471)
        ·
          refine ⟨40992254372080189039989707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27328169581386792693326471 40992254372080189039989707)
          ·
            refine ⟨61488381558120283559984561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40992254372080189039989707 61488381558120283559984561)
            ·
              refine ⟨46116286168590212669988421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61488381558120283559984561 46116286168590212669988421)
              ·
                refine ⟨8646803656610664875622829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46116286168590212669988421 8646803656610664875622829)
                ·
                  refine ⟨3242551371228999328358561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8646803656610664875622829 3242551371228999328358561)
                  ·
                    refine ⟨2431913528421749496268921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3242551371228999328358561 2431913528421749496268921)
                    ·
                      refine ⟨1823935146316312122201691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2431913528421749496268921 1823935146316312122201691)
                      ·
                        rfl

theorem cell23_3552101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4, 3, 2, 2].length) (baseStart_3552101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3552101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3552101 prefixEnd_3552101 := by exact prefixLift 3552101
  have htrace : WordTrace (prefixWord ++ tailWord_3552101) baseStart_3552101 baseEnd_3552101 := by
    simpa [prefixWord, tailWord_3552101, baseEnd_3552101] using wordTrace_append hprefix tailTrace_3552101
  have hstable : (prefixWord ++ tailWord_3552101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552101).length < 2 ^ (prefixWord ++ tailWord_3552101).sum := by decide
  have hdescent : baseEnd_3552101 < baseStart_3552101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552135 : List Nat := [1, 1, 4, 2, 3, 2, 1, 4, 1, 2, 2]
def baseStart_3552135 : Nat := 118140960795 + 3552135 * 2 ^ 59
def prefixEnd_3552135 : Nat := 4983230072969 + 3 ^ 40 * 3552135 * 2
def baseEnd_3552135 : Nat := 1823952604658564989176535

theorem tailTrace_3552135 : CollatzResearch.WordTrace tailWord_3552135 prefixEnd_3552135 1823952604658564989176535 := by
  unfold tailWord_3552135
  simp only [CollatzResearch.WordTrace]
  refine ⟨129557006986229026204729859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86371337990819350803153239 129557006986229026204729859)
  ·
    refine ⟨194335510479343539307094789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129557006986229026204729859 194335510479343539307094789)
    ·
      refine ⟨36437908214876913620080273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194335510479343539307094789 36437908214876913620080273)
      ·
        refine ⟨27328431161157685215060205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36437908214876913620080273 27328431161157685215060205)
        ·
          refine ⟨10248161685434131955647577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27328431161157685215060205 10248161685434131955647577)
          ·
            refine ⟨7686121264075598966735683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10248161685434131955647577 7686121264075598966735683)
            ·
              refine ⟨11529181896113398450103525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7686121264075598966735683 11529181896113398450103525)
              ·
                refine ⟨2161721605521262209394411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11529181896113398450103525 2161721605521262209394411)
                ·
                  refine ⟨3242582408281893314091617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2161721605521262209394411 3242582408281893314091617)
                  ·
                    refine ⟨2431936806211419985568713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3242582408281893314091617 2431936806211419985568713)
                    ·
                      refine ⟨1823952604658564989176535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2431936806211419985568713 1823952604658564989176535)
                      ·
                        rfl

theorem cell23_3552135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 4, 1, 2, 2].length) (baseStart_3552135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3552135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3552135 prefixEnd_3552135 := by exact prefixLift 3552135
  have htrace : WordTrace (prefixWord ++ tailWord_3552135) baseStart_3552135 baseEnd_3552135 := by
    simpa [prefixWord, tailWord_3552135, baseEnd_3552135] using wordTrace_append hprefix tailTrace_3552135
  have hstable : (prefixWord ++ tailWord_3552135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552135).length < 2 ^ (prefixWord ++ tailWord_3552135).sum := by decide
  have hdescent : baseEnd_3552135 < baseStart_3552135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552137 : List Nat := [1, 2, 1, 1, 5, 2, 1, 1, 2, 7]
def baseStart_3552137 : Nat := 118140960795 + 3552137 * 2 ^ 59
def prefixEnd_3552137 : Nat := 4983230072969 + 3 ^ 40 * 3552137 * 2
def baseEnd_3552137 : Nat := 607984543873291327117175

theorem tailTrace_3552137 : CollatzResearch.WordTrace tailWord_3552137 prefixEnd_3552137 607984543873291327117175 := by
  unfold tailWord_3552137
  simp only [CollatzResearch.WordTrace]
  refine ⟨129557079932221780546302665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86371386621481187030868443 129557079932221780546302665)
  ·
    refine ⟨97167809949166335409726999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129557079932221780546302665 97167809949166335409726999)
    ·
      refine ⟨145751714923749503114590499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97167809949166335409726999 145751714923749503114590499)
      ·
        refine ⟨218627572385624254671885749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145751714923749503114590499 218627572385624254671885749)
        ·
          refine ⟨20496334911152273875489289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 218627572385624254671885749 20496334911152273875489289)
          ·
            refine ⟨15372251183364205406616967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20496334911152273875489289 15372251183364205406616967)
            ·
              refine ⟨23058376775046308109925451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15372251183364205406616967 23058376775046308109925451)
              ·
                refine ⟨34587565162569462164888177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23058376775046308109925451 34587565162569462164888177)
                ·
                  refine ⟨25940673871927096623666133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34587565162569462164888177 25940673871927096623666133)
                  ·
                    refine ⟨607984543873291327117175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25940673871927096623666133 607984543873291327117175)
                    ·
                      rfl

theorem cell23_3552137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 7].length) (baseStart_3552137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3552137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3552137 prefixEnd_3552137 := by exact prefixLift 3552137
  have htrace : WordTrace (prefixWord ++ tailWord_3552137) baseStart_3552137 baseEnd_3552137 := by
    simpa [prefixWord, tailWord_3552137, baseEnd_3552137] using wordTrace_append hprefix tailTrace_3552137
  have hstable : (prefixWord ++ tailWord_3552137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552137).length < 2 ^ (prefixWord ++ tailWord_3552137).sum := by decide
  have hdescent : baseEnd_3552137 < baseStart_3552137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552151 : List Nat := [1, 1, 3, 3, 1, 2, 1, 5, 2, 1, 3]
def baseStart_3552151 : Nat := 118140960795 + 3552151 * 2 ^ 59
def prefixEnd_3552151 : Nat := 4983230072969 + 3 ^ 40 * 3552151 * 2
def baseEnd_3552151 : Nat := 1823960820349036926576461

theorem tailTrace_3552151 : CollatzResearch.WordTrace tailWord_3552151 prefixEnd_3552151 1823960820349036926576461 := by
  unfold tailWord_3552151
  simp only [CollatzResearch.WordTrace]
  refine ⟨129557590554171060937312307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86371727036114040624874871 129557590554171060937312307)
  ·
    refine ⟨194336385831256591405968461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129557590554171060937312307 194336385831256591405968461)
    ·
      refine ⟨72876144686721221777238173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194336385831256591405968461 72876144686721221777238173)
      ·
        refine ⟨27328554257520458166464315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72876144686721221777238173 27328554257520458166464315)
        ·
          refine ⟨40992831386280687249696473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27328554257520458166464315 40992831386280687249696473)
          ·
            refine ⟨30744623539710515437272355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40992831386280687249696473 30744623539710515437272355)
            ·
              refine ⟨46116935309565773155908533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30744623539710515437272355 46116935309565773155908533)
              ·
                refine ⟨4323462685271791233366425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46116935309565773155908533 4323462685271791233366425)
                ·
                  refine ⟨3242597013953843425024819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4323462685271791233366425 3242597013953843425024819)
                  ·
                    refine ⟨4863895520930765137537229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3242597013953843425024819 4863895520930765137537229)
                    ·
                      refine ⟨1823960820349036926576461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4863895520930765137537229 1823960820349036926576461)
                      ·
                        rfl

theorem cell23_3552151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 5, 2, 1, 3].length) (baseStart_3552151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3552151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3552151 prefixEnd_3552151 := by exact prefixLift 3552151
  have htrace : WordTrace (prefixWord ++ tailWord_3552151) baseStart_3552151 baseEnd_3552151 := by
    simpa [prefixWord, tailWord_3552151, baseEnd_3552151] using wordTrace_append hprefix tailTrace_3552151
  have hstable : (prefixWord ++ tailWord_3552151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552151).length < 2 ^ (prefixWord ++ tailWord_3552151).sum := by decide
  have hdescent : baseEnd_3552151 < baseStart_3552151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552204 : List Nat := [2, 2, 1, 4, 1, 1, 1, 3, 2, 2, 4]
def baseStart_3552204 : Nat := 118140960795 + 3552204 * 2 ^ 59
def prefixEnd_3552204 : Nat := 4983230072969 + 3 ^ 40 * 3552204 * 2
def baseEnd_3552204 : Nat := 1823988034823725219213717

theorem tailTrace_3552204 : CollatzResearch.WordTrace tailWord_3552204 prefixEnd_3552204 1823988034823725219213717 := by
  unfold tailWord_3552204
  simp only [CollatzResearch.WordTrace]
  refine ⟨64779761811489525494495833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86373015748652700659327777 64779761811489525494495833)
  ·
    refine ⟨48584821358617144120871875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64779761811489525494495833 48584821358617144120871875)
    ·
      refine ⟨72877232037925716181307813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48584821358617144120871875 72877232037925716181307813)
      ·
        refine ⟨13664481007111071783995215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72877232037925716181307813 13664481007111071783995215)
        ·
          refine ⟨20496721510666607675992823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13664481007111071783995215 20496721510666607675992823)
          ·
            refine ⟨30745082265999911513989235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20496721510666607675992823 30745082265999911513989235)
            ·
              refine ⟨46117623398999867270983853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30745082265999911513989235 46117623398999867270983853)
              ·
                refine ⟨17294108774624950226618945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46117623398999867270983853 17294108774624950226618945)
                ·
                  refine ⟨12970581580968712669964209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17294108774624950226618945 12970581580968712669964209)
                  ·
                    refine ⟨9727936185726534502473157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12970581580968712669964209 9727936185726534502473157)
                    ·
                      refine ⟨1823988034823725219213717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9727936185726534502473157 1823988034823725219213717)
                      ·
                        rfl

theorem cell23_3552204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_3552204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3552204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3552204 prefixEnd_3552204 := by exact prefixLift 3552204
  have htrace : WordTrace (prefixWord ++ tailWord_3552204) baseStart_3552204 baseEnd_3552204 := by
    simpa [prefixWord, tailWord_3552204, baseEnd_3552204] using wordTrace_append hprefix tailTrace_3552204
  have hstable : (prefixWord ++ tailWord_3552204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552204).length < 2 ^ (prefixWord ++ tailWord_3552204).sum := by decide
  have hdescent : baseEnd_3552204 < baseStart_3552204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552247 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 8]
def baseStart_3552247 : Nat := 118140960795 + 3552247 * 2 ^ 59
def prefixEnd_3552247 : Nat := 4983230072969 + 3 ^ 40 * 3552247 * 2
def baseEnd_3552247 : Nat := 1824010114491868550976019

theorem tailTrace_3552247 : CollatzResearch.WordTrace tailWord_3552247 prefixEnd_3552247 1824010114491868550976019 := by
  unfold tailWord_3552247
  simp only [CollatzResearch.WordTrace]
  refine ⟨129561091961823269332806995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86374061307882179555204663 129561091961823269332806995)
  ·
    refine ⟨194341637942734903999210493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129561091961823269332806995 194341637942734903999210493)
    ·
      refine ⟨72878114228525588999703935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194341637942734903999210493 72878114228525588999703935)
      ·
        refine ⟨109317171342788383499555903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72878114228525588999703935 109317171342788383499555903)
        ·
          refine ⟨163975757014182575249333855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109317171342788383499555903 163975757014182575249333855)
          ·
            refine ⟨245963635521273862874000783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163975757014182575249333855 245963635521273862874000783)
            ·
              refine ⟨368945453281910794311001175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245963635521273862874000783 368945453281910794311001175)
              ·
                refine ⟨553418179922866191466501763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 368945453281910794311001175 553418179922866191466501763)
                ·
                  refine ⟨830127269884299287199752645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 553418179922866191466501763 830127269884299287199752645)
                  ·
                    refine ⟨155648863103306116349953621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 830127269884299287199752645 155648863103306116349953621)
                    ·
                      refine ⟨1824010114491868550976019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 155648863103306116349953621 1824010114491868550976019)
                      ·
                        rfl

theorem cell23_3552247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 8].length) (baseStart_3552247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3552247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3552247 prefixEnd_3552247 := by exact prefixLift 3552247
  have htrace : WordTrace (prefixWord ++ tailWord_3552247) baseStart_3552247 baseEnd_3552247 := by
    simpa [prefixWord, tailWord_3552247, baseEnd_3552247] using wordTrace_append hprefix tailTrace_3552247
  have hstable : (prefixWord ++ tailWord_3552247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552247).length < 2 ^ (prefixWord ++ tailWord_3552247).sum := by decide
  have hdescent : baseEnd_3552247 < baseStart_3552247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552348 : List Nat := [2, 2, 4, 1, 1, 1, 1, 2, 5, 1, 3]
def baseStart_3552348 : Nat := 118140960795 + 3552348 * 2 ^ 59
def prefixEnd_3552348 : Nat := 4983230072969 + 3 ^ 40 * 3552348 * 2
def baseEnd_3552348 : Nat := 1824061976037972655813055

theorem tailTrace_3552348 : CollatzResearch.WordTrace tailWord_3552348 prefixEnd_3552348 1824061976037972655813055 := by
  unfold tailWord_3552348
  simp only [CollatzResearch.WordTrace]
  refine ⟨64782387867228681791116849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86376517156304909054822465 64782387867228681791116849)
  ·
    refine ⟨48586790900421511343337637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64782387867228681791116849 48586790900421511343337637)
    ·
      refine ⟨9110023293829033376875807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48586790900421511343337637 9110023293829033376875807)
      ·
        refine ⟨13665034940743550065313711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9110023293829033376875807 13665034940743550065313711)
        ·
          refine ⟨20497552411115325097970567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13665034940743550065313711 20497552411115325097970567)
          ·
            refine ⟨30746328616672987646955851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20497552411115325097970567 30746328616672987646955851)
            ·
              refine ⟨46119492925009481470433777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30746328616672987646955851 46119492925009481470433777)
              ·
                refine ⟨34589619693757111102825333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46119492925009481470433777 34589619693757111102825333)
                ·
                  refine ⟨3242776846289729165889875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34589619693757111102825333 3242776846289729165889875)
                  ·
                    refine ⟨4864165269434593748834813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3242776846289729165889875 4864165269434593748834813)
                    ·
                      refine ⟨1824061976037972655813055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4864165269434593748834813 1824061976037972655813055)
                      ·
                        rfl

theorem cell23_3552348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_3552348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3552348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3552348 prefixEnd_3552348 := by exact prefixLift 3552348
  have htrace : WordTrace (prefixWord ++ tailWord_3552348) baseStart_3552348 baseEnd_3552348 := by
    simpa [prefixWord, tailWord_3552348, baseEnd_3552348] using wordTrace_append hprefix tailTrace_3552348
  have hstable : (prefixWord ++ tailWord_3552348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552348).length < 2 ^ (prefixWord ++ tailWord_3552348).sum := by decide
  have hdescent : baseEnd_3552348 < baseStart_3552348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552351 : List Nat := [1, 1, 2, 3, 1, 1, 5, 3, 1, 5]
def baseStart_3552351 : Nat := 118140960795 + 3552351 * 2 ^ 59
def prefixEnd_3552351 : Nat := 4983230072969 + 3 ^ 40 * 3552351 * 2
def baseEnd_3552351 : Nat := 608021172159978714691847

theorem tailTrace_3552351 : CollatzResearch.WordTrace tailWord_3552351 prefixEnd_3552351 608021172159978714691847 := by
  unfold tailWord_3552351
  simp only [CollatzResearch.WordTrace]
  refine ⟨129564885153446495094592907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86376590102297663396395271 129564885153446495094592907)
  ·
    refine ⟨194347327730169742641889361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129564885153446495094592907 194347327730169742641889361)
    ·
      refine ⟨145760495797627306981417021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194347327730169742641889361 145760495797627306981417021)
      ·
        refine ⟨54660185924110240118031383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145760495797627306981417021 54660185924110240118031383)
        ·
          refine ⟨81990278886165360177047075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54660185924110240118031383 81990278886165360177047075)
          ·
            refine ⟨122985418329248040265570613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81990278886165360177047075 122985418329248040265570613)
            ·
              refine ⟨11529882968367003774897245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 122985418329248040265570613 11529882968367003774897245)
              ·
                refine ⟨4323706113137626415586467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11529882968367003774897245 4323706113137626415586467)
                ·
                  refine ⟨6485559169706439623379701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4323706113137626415586467 6485559169706439623379701)
                  ·
                    refine ⟨608021172159978714691847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6485559169706439623379701 608021172159978714691847)
                    ·
                      rfl

theorem cell23_3552351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 3, 1, 5].length) (baseStart_3552351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3552351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3552351 prefixEnd_3552351 := by exact prefixLift 3552351
  have htrace : WordTrace (prefixWord ++ tailWord_3552351) baseStart_3552351 baseEnd_3552351 := by
    simpa [prefixWord, tailWord_3552351, baseEnd_3552351] using wordTrace_append hprefix tailTrace_3552351
  have hstable : (prefixWord ++ tailWord_3552351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552351).length < 2 ^ (prefixWord ++ tailWord_3552351).sum := by decide
  have hdescent : baseEnd_3552351 < baseStart_3552351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552365 : List Nat := [1, 5, 1, 1, 2, 3, 2, 1, 3, 1, 3]
def baseStart_3552365 : Nat := 118140960795 + 3552365 * 2 ^ 59
def prefixEnd_3552365 : Nat := 4983230072969 + 3 ^ 40 * 3552365 * 2
def baseEnd_3552365 : Nat := 1824070705209099089300477

theorem tailTrace_3552365 : CollatzResearch.WordTrace tailWord_3552365 prefixEnd_3552365 1824070705209099089300477 := by
  unfold tailWord_3552365
  simp only [CollatzResearch.WordTrace]
  refine ⟨129565395775395775485602549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86376930516930516990401699 129565395775395775485602549)
  ·
    refine ⟨12146755853943353951775239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 129565395775395775485602549 12146755853943353951775239)
    ·
      refine ⟨18220133780915030927662859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12146755853943353951775239 18220133780915030927662859)
      ·
        refine ⟨27330200671372546391494289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18220133780915030927662859 27330200671372546391494289)
        ·
          refine ⟨20497650503529409793620717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27330200671372546391494289 20497650503529409793620717)
          ·
            refine ⟨7686618938823528672607769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20497650503529409793620717 7686618938823528672607769)
            ·
              refine ⟨5764964204117646504455827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7686618938823528672607769 5764964204117646504455827)
              ·
                refine ⟨8647446306176469756683741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5764964204117646504455827 8647446306176469756683741)
                ·
                  refine ⟨3242792364816176158756403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8647446306176469756683741 3242792364816176158756403)
                  ·
                    refine ⟨4864188547224264238134605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3242792364816176158756403 4864188547224264238134605)
                    ·
                      refine ⟨1824070705209099089300477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4864188547224264238134605 1824070705209099089300477)
                      ·
                        rfl

theorem cell23_3552365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 1, 3, 1, 3].length) (baseStart_3552365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3552365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3552365 prefixEnd_3552365 := by exact prefixLift 3552365
  have htrace : WordTrace (prefixWord ++ tailWord_3552365) baseStart_3552365 baseEnd_3552365 := by
    simpa [prefixWord, tailWord_3552365, baseEnd_3552365] using wordTrace_append hprefix tailTrace_3552365
  have hstable : (prefixWord ++ tailWord_3552365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552365).length < 2 ^ (prefixWord ++ tailWord_3552365).sum := by decide
  have hdescent : baseEnd_3552365 < baseStart_3552365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552388 : List Nat := [2, 3, 2, 1, 2, 2, 1, 4, 1, 1, 4]
def baseStart_3552388 : Nat := 118140960795 + 3552388 * 2 ^ 59
def prefixEnd_3552388 : Nat := 4983230072969 + 3 ^ 40 * 3552388 * 2
def baseEnd_3552388 : Nat := 1824082515264152499312871

theorem tailTrace_3552388 : CollatzResearch.WordTrace tailWord_3552388 prefixEnd_3552388 1824082515264152499312871 := by
  unfold tailWord_3552388
  simp only [CollatzResearch.WordTrace]
  refine ⟨64783117327156225206844909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86377489769541633609126545 64783117327156225206844909)
  ·
    refine ⟨24293668997683584452566841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64783117327156225206844909 24293668997683584452566841)
    ·
      refine ⟨18220251748262688339425131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24293668997683584452566841 18220251748262688339425131)
      ·
        refine ⟨27330377622394032509137697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18220251748262688339425131 27330377622394032509137697)
        ·
          refine ⟨20497783216795524381853273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27330377622394032509137697 20497783216795524381853273)
          ·
            refine ⟨15373337412596643286389955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20497783216795524381853273 15373337412596643286389955)
            ·
              refine ⟨23060006118894964929584933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15373337412596643286389955 23060006118894964929584933)
              ·
                refine ⟨4323751147292805924297175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23060006118894964929584933 4323751147292805924297175)
                ·
                  refine ⟨6485626720939208886445763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4323751147292805924297175 6485626720939208886445763)
                  ·
                    refine ⟨9728440081408813329668645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6485626720939208886445763 9728440081408813329668645)
                    ·
                      refine ⟨1824082515264152499312871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9728440081408813329668645 1824082515264152499312871)
                      ·
                        rfl

theorem cell23_3552388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 4, 1, 1, 4].length) (baseStart_3552388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3552388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3552388 prefixEnd_3552388 := by exact prefixLift 3552388
  have htrace : WordTrace (prefixWord ++ tailWord_3552388) baseStart_3552388 baseEnd_3552388 := by
    simpa [prefixWord, tailWord_3552388, baseEnd_3552388] using wordTrace_append hprefix tailTrace_3552388
  have hstable : (prefixWord ++ tailWord_3552388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552388).length < 2 ^ (prefixWord ++ tailWord_3552388).sum := by decide
  have hdescent : baseEnd_3552388 < baseStart_3552388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552398 : List Nat := [4, 1, 1, 3, 2, 1, 1, 2, 4, 4]
def baseStart_3552398 : Nat := 118140960795 + 3552398 * 2 ^ 59
def prefixEnd_3552398 : Nat := 4983230072969 + 3 ^ 40 * 3552398 * 2
def baseEnd_3552398 : Nat := 608029216690232486729275

theorem tailTrace_3552398 : CollatzResearch.WordTrace tailWord_3552398 prefixEnd_3552398 608029216690232486729275 := by
  unfold tailWord_3552398
  simp only [CollatzResearch.WordTrace]
  refine ⟨16195824923034527765194231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86377732922850814747702565 16195824923034527765194231)
  ·
    refine ⟨24293737384551791647791347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16195824923034527765194231 24293737384551791647791347)
    ·
      refine ⟨36440606076827687471687021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24293737384551791647791347 36440606076827687471687021)
      ·
        refine ⟨13665227278810382801882633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36440606076827687471687021 13665227278810382801882633)
        ·
          refine ⟨10248920459107787101411975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13665227278810382801882633 10248920459107787101411975)
          ·
            refine ⟨15373380688661680652117963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10248920459107787101411975 15373380688661680652117963)
            ·
              refine ⟨23060071032992520978176945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15373380688661680652117963 23060071032992520978176945)
              ·
                refine ⟨17295053274744390733632709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23060071032992520978176945 17295053274744390733632709)
                ·
                  refine ⟨3242822489014573262556133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17295053274744390733632709 3242822489014573262556133)
                  ·
                    refine ⟨608029216690232486729275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3242822489014573262556133 608029216690232486729275)
                    ·
                      rfl

theorem cell23_3552398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 4, 4].length) (baseStart_3552398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3552398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3552398 prefixEnd_3552398 := by exact prefixLift 3552398
  have htrace : WordTrace (prefixWord ++ tailWord_3552398) baseStart_3552398 baseEnd_3552398 := by
    simpa [prefixWord, tailWord_3552398, baseEnd_3552398] using wordTrace_append hprefix tailTrace_3552398
  have hstable : (prefixWord ++ tailWord_3552398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552398).length < 2 ^ (prefixWord ++ tailWord_3552398).sum := by decide
  have hdescent : baseEnd_3552398 < baseStart_3552398 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552408 : List Nat := [2, 1, 2, 4, 2, 2, 2, 1, 1, 1, 5]
def baseStart_3552408 : Nat := 118140960795 + 3552408 * 2 ^ 59
def prefixEnd_3552408 : Nat := 4983230072969 + 3 ^ 40 * 3552408 * 2
def baseEnd_3552408 : Nat := 1824092784877242421062779

theorem tailTrace_3552408 : CollatzResearch.WordTrace tailWord_3552408 prefixEnd_3552408 1824092784877242421062779 := by
  unfold tailWord_3552408
  simp only [CollatzResearch.WordTrace]
  refine ⟨64783482057119996914708939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86377976076159995886278585 64783482057119996914708939)
  ·
    refine ⟨97175223085679995372063409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64783482057119996914708939 97175223085679995372063409)
    ·
      refine ⟨72881417314259996529047557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97175223085679995372063409 72881417314259996529047557)
      ·
        refine ⟨13665265746423749349196417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72881417314259996529047557 13665265746423749349196417)
        ·
          refine ⟨10248949309817812011897313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13665265746423749349196417 10248949309817812011897313)
          ·
            refine ⟨7686711982363359008922985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10248949309817812011897313 7686711982363359008922985)
            ·
              refine ⟨5765033986772519256692239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7686711982363359008922985 5765033986772519256692239)
              ·
                refine ⟨8647550980158778885038359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5765033986772519256692239 8647550980158778885038359)
                ·
                  refine ⟨12971326470238168327557539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8647550980158778885038359 12971326470238168327557539)
                  ·
                    refine ⟨19456989705357252491336309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12971326470238168327557539 19456989705357252491336309)
                    ·
                      refine ⟨1824092784877242421062779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19456989705357252491336309 1824092784877242421062779)
                      ·
                        rfl

theorem cell23_3552408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_3552408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3552408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3552408 prefixEnd_3552408 := by exact prefixLift 3552408
  have htrace : WordTrace (prefixWord ++ tailWord_3552408) baseStart_3552408 baseEnd_3552408 := by
    simpa [prefixWord, tailWord_3552408, baseEnd_3552408] using wordTrace_append hprefix tailTrace_3552408
  have hstable : (prefixWord ++ tailWord_3552408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552408).length < 2 ^ (prefixWord ++ tailWord_3552408).sum := by decide
  have hdescent : baseEnd_3552408 < baseStart_3552408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552472 : List Nat := [2, 1, 2, 2, 5, 1, 2, 2, 2, 1, 3]
def baseStart_3552472 : Nat := 118140960795 + 3552472 * 2 ^ 59
def prefixEnd_3552472 : Nat := 4983230072969 + 3 ^ 40 * 3552472 * 2
def baseEnd_3552472 : Nat := 1824125647639130170662485

theorem tailTrace_3552472 : CollatzResearch.WordTrace tailWord_3552472 prefixEnd_3552472 1824125647639130170662485 := by
  unfold tailWord_3552472
  simp only [CollatzResearch.WordTrace]
  refine ⟨64784649193004066379873835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86379532257338755173165113 64784649193004066379873835)
  ·
    refine ⟨97176973789506099569810753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64784649193004066379873835 97176973789506099569810753)
    ·
      refine ⟨72882730342129574677358065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97176973789506099569810753 72882730342129574677358065)
      ·
        refine ⟨54662047756597181008018549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72882730342129574677358065 54662047756597181008018549)
        ·
          refine ⟨5124566977180985719501739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54662047756597181008018549 5124566977180985719501739)
          ·
            refine ⟨7686850465771478579252609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5124566977180985719501739 7686850465771478579252609)
            ·
              refine ⟨5765137849328608934439457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7686850465771478579252609 5765137849328608934439457)
              ·
                refine ⟨4323853386996456700829593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5765137849328608934439457 4323853386996456700829593)
                ·
                  refine ⟨3242890040247342525622195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4323853386996456700829593 3242890040247342525622195)
                  ·
                    refine ⟨4864335060371013788433293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3242890040247342525622195 4864335060371013788433293)
                    ·
                      refine ⟨1824125647639130170662485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4864335060371013788433293 1824125647639130170662485)
                      ·
                        rfl

theorem cell23_3552472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 2, 2, 1, 3].length) (baseStart_3552472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3552472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3552472 prefixEnd_3552472 := by exact prefixLift 3552472
  have htrace : WordTrace (prefixWord ++ tailWord_3552472) baseStart_3552472 baseEnd_3552472 := by
    simpa [prefixWord, tailWord_3552472, baseEnd_3552472] using wordTrace_append hprefix tailTrace_3552472
  have hstable : (prefixWord ++ tailWord_3552472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552472).length < 2 ^ (prefixWord ++ tailWord_3552472).sum := by decide
  have hdescent : baseEnd_3552472 < baseStart_3552472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552491 : List Nat := [1, 1, 1, 1, 2, 6, 1, 1, 1, 4, 4]
def baseStart_3552491 : Nat := 118140960795 + 3552491 * 2 ^ 59
def prefixEnd_3552491 : Nat := 4983230072969 + 3 ^ 40 * 3552491 * 2
def baseEnd_3552491 : Nat := 1824135403771565596324897

theorem tailTrace_3552491 : CollatzResearch.WordTrace tailWord_3552491 prefixEnd_3552491 1824135403771565596324897 := by
  unfold tailWord_3552491
  simp only [CollatzResearch.WordTrace]
  refine ⟨129569991372939299004689327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86379994248626199336459551 129569991372939299004689327)
  ·
    refine ⟨194354987059408948507033991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129569991372939299004689327 194354987059408948507033991)
    ·
      refine ⟨291532480589113422760550987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194354987059408948507033991 291532480589113422760550987)
      ·
        refine ⟨437298720883670134140826481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291532480589113422760550987 437298720883670134140826481)
        ·
          refine ⟨327974040662752600605619861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 437298720883670134140826481 327974040662752600605619861)
          ·
            refine ⟨15373783156066528153388431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 327974040662752600605619861 15373783156066528153388431)
            ·
              refine ⟨23060674734099792230082647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15373783156066528153388431 23060674734099792230082647)
              ·
                refine ⟨34591012101149688345123971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23060674734099792230082647 34591012101149688345123971)
                ·
                  refine ⟨51886518151724532517685957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34591012101149688345123971 51886518151724532517685957)
                  ·
                    refine ⟨9728722153448349847066117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51886518151724532517685957 9728722153448349847066117)
                    ·
                      refine ⟨1824135403771565596324897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9728722153448349847066117 1824135403771565596324897)
                      ·
                        rfl

theorem cell23_3552491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 4, 4].length) (baseStart_3552491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3552491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3552491 prefixEnd_3552491 := by exact prefixLift 3552491
  have htrace : WordTrace (prefixWord ++ tailWord_3552491) baseStart_3552491 baseEnd_3552491 := by
    simpa [prefixWord, tailWord_3552491, baseEnd_3552491] using wordTrace_append hprefix tailTrace_3552491
  have hstable : (prefixWord ++ tailWord_3552491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552491).length < 2 ^ (prefixWord ++ tailWord_3552491).sum := by decide
  have hdescent : baseEnd_3552491 < baseStart_3552491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552546 : List Nat := [3, 3, 1, 1, 4, 1, 3, 1, 2, 2, 2]
def baseStart_3552546 : Nat := 118140960795 + 3552546 * 2 ^ 59
def prefixEnd_3552546 : Nat := 4983230072969 + 3 ^ 40 * 3552546 * 2
def baseEnd_3552546 : Nat := 1824163645207562881137145

theorem tailTrace_3552546 : CollatzResearch.WordTrace tailWord_3552546 prefixEnd_3552546 1824163645207562881137145 := by
  unfold tailWord_3552546
  simp only [CollatzResearch.WordTrace]
  refine ⟨32392999346935010849485373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86381331591826695598627661 32392999346935010849485373)
  ·
    refine ⟨12147374755100629068557015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32392999346935010849485373 12147374755100629068557015)
    ·
      refine ⟨18221062132650943602835523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12147374755100629068557015 18221062132650943602835523)
      ·
        refine ⟨27331593198976415404253285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18221062132650943602835523 27331593198976415404253285)
        ·
          refine ⟨5124673724808077888297491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27331593198976415404253285 5124673724808077888297491)
          ·
            refine ⟨7687010587212116832446237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5124673724808077888297491 7687010587212116832446237)
            ·
              refine ⟨2882628970204543812167339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7687010587212116832446237 2882628970204543812167339)
              ·
                refine ⟨4323943455306815718251009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2882628970204543812167339 4323943455306815718251009)
                ·
                  refine ⟨3242957591480111788688257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4323943455306815718251009 3242957591480111788688257)
                  ·
                    refine ⟨2432218193610083841516193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3242957591480111788688257 2432218193610083841516193)
                    ·
                      refine ⟨1824163645207562881137145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2432218193610083841516193 1824163645207562881137145)
                      ·
                        rfl

theorem cell23_3552546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3, 1, 2, 2, 2].length) (baseStart_3552546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3552546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3552546 prefixEnd_3552546 := by exact prefixLift 3552546
  have htrace : WordTrace (prefixWord ++ tailWord_3552546) baseStart_3552546 baseEnd_3552546 := by
    simpa [prefixWord, tailWord_3552546, baseEnd_3552546] using wordTrace_append hprefix tailTrace_3552546
  have hstable : (prefixWord ++ tailWord_3552546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552546).length < 2 ^ (prefixWord ++ tailWord_3552546).sum := by decide
  have hdescent : baseEnd_3552546 < baseStart_3552546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552568 : List Nat := [2, 1, 2, 1, 3, 1, 1, 5, 2, 1, 4]
def baseStart_3552568 : Nat := 118140960795 + 3552568 * 2 ^ 59
def prefixEnd_3552568 : Nat := 4983230072969 + 3 ^ 40 * 3552568 * 2
def baseEnd_3552568 : Nat := 1824174941781961795062043

theorem tailTrace_3552568 : CollatzResearch.WordTrace tailWord_3552568 prefixEnd_3552568 1824174941781961795062043 := by
  unfold tailWord_3552568
  simp only [CollatzResearch.WordTrace]
  refine ⟨64786399896830170577621179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86381866529106894103494905 64786399896830170577621179)
  ·
    refine ⟨97179599845245255866431769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64786399896830170577621179 97179599845245255866431769)
    ·
      refine ⟨72884699883933941899823827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97179599845245255866431769 72884699883933941899823827)
      ·
        refine ⟨109327049825900912849735741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72884699883933941899823827 109327049825900912849735741)
        ·
          refine ⟨40997643684712842318650903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109327049825900912849735741 40997643684712842318650903)
          ·
            refine ⟨61496465527069263477976355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40997643684712842318650903 61496465527069263477976355)
            ·
              refine ⟨92244698290603895216964533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61496465527069263477976355 92244698290603895216964533)
              ·
                refine ⟨8647940464744115176590425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92244698290603895216964533 8647940464744115176590425)
                ·
                  refine ⟨6485955348558086382442819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8647940464744115176590425 6485955348558086382442819)
                  ·
                    refine ⟨9728933022837129573664229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6485955348558086382442819 9728933022837129573664229)
                    ·
                      refine ⟨1824174941781961795062043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9728933022837129573664229 1824174941781961795062043)
                      ·
                        rfl

theorem cell23_3552568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5, 2, 1, 4].length) (baseStart_3552568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3552568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3552568 prefixEnd_3552568 := by exact prefixLift 3552568
  have htrace : WordTrace (prefixWord ++ tailWord_3552568) baseStart_3552568 baseEnd_3552568 := by
    simpa [prefixWord, tailWord_3552568, baseEnd_3552568] using wordTrace_append hprefix tailTrace_3552568
  have hstable : (prefixWord ++ tailWord_3552568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552568).length < 2 ^ (prefixWord ++ tailWord_3552568).sum := by decide
  have hdescent : baseEnd_3552568 < baseStart_3552568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552569 : List Nat := [1, 2, 1, 6, 3, 1, 1, 3, 5]
def baseStart_3552569 : Nat := 118140960795 + 3552569 * 2 ^ 59
def prefixEnd_3552569 : Nat := 4983230072969 + 3 ^ 40 * 3552569 * 2
def baseEnd_3552569 : Nat := 202686161695846254572171

theorem tailTrace_3552569 : CollatzResearch.WordTrace tailWord_3552569 prefixEnd_3552569 202686161695846254572171 := by
  unfold tailWord_3552569
  simp only [CollatzResearch.WordTrace]
  refine ⟨129572836266656718326028761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86381890844437812217352507 129572836266656718326028761)
  ·
    refine ⟨97179627199992538744521571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129572836266656718326028761 97179627199992538744521571)
    ·
      refine ⟨145769440799988808116782357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97179627199992538744521571 145769440799988808116782357)
      ·
        refine ⟨6832942537499475380474173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 145769440799988808116782357 6832942537499475380474173)
        ·
          refine ⟨2562353451562303267677815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6832942537499475380474173 2562353451562303267677815)
          ·
            refine ⟨3843530177343454901516723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2562353451562303267677815 3843530177343454901516723)
            ·
              refine ⟨5765295266015182352275085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3843530177343454901516723 5765295266015182352275085)
              ·
                refine ⟨2161985724755693382103157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5765295266015182352275085 2161985724755693382103157)
                ·
                  refine ⟨202686161695846254572171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2161985724755693382103157 202686161695846254572171)
                  ·
                    rfl

theorem cell23_3552569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 3, 5].length) (baseStart_3552569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3552569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3552569 prefixEnd_3552569 := by exact prefixLift 3552569
  have htrace : WordTrace (prefixWord ++ tailWord_3552569) baseStart_3552569 baseEnd_3552569 := by
    simpa [prefixWord, tailWord_3552569, baseEnd_3552569] using wordTrace_append hprefix tailTrace_3552569
  have hstable : (prefixWord ++ tailWord_3552569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552569).length < 2 ^ (prefixWord ++ tailWord_3552569).sum := by decide
  have hdescent : baseEnd_3552569 < baseStart_3552569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552581 : List Nat := [1, 3, 1, 1, 1, 2, 1, 3, 1, 3, 6]
def baseStart_3552581 : Nat := 118140960795 + 3552581 * 2 ^ 59
def prefixEnd_3552581 : Nat := 4983230072969 + 3 ^ 40 * 3552581 * 2
def baseEnd_3552581 : Nat := 1824181617030470244199483

theorem tailTrace_3552581 : CollatzResearch.WordTrace tailWord_3552581 prefixEnd_3552581 1824181617030470244199483 := by
  unfold tailWord_3552581
  simp only [CollatzResearch.WordTrace]
  refine ⟨129573273942613244375465597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86382182628408829583643731 129573273942613244375465597)
  ·
    refine ⟨48589977728479966640799599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129573273942613244375465597 48589977728479966640799599)
    ·
      refine ⟨72884966592719949961199399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48589977728479966640799599 72884966592719949961199399)
      ·
        refine ⟨109327449889079924941799099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72884966592719949961199399 109327449889079924941799099)
        ·
          refine ⟨163991174833619887412698649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109327449889079924941799099 163991174833619887412698649)
          ·
            refine ⟨122993381125214915559523987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163991174833619887412698649 122993381125214915559523987)
            ·
              refine ⟨184490071687822373339285981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122993381125214915559523987 184490071687822373339285981)
              ·
                refine ⟨69183776882933390002232243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 184490071687822373339285981 69183776882933390002232243)
                ·
                  refine ⟨103775665324400085003348365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69183776882933390002232243 103775665324400085003348365)
                  ·
                    refine ⟨38915874496650031876255637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 103775665324400085003348365 38915874496650031876255637)
                    ·
                      refine ⟨1824181617030470244199483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38915874496650031876255637 1824181617030470244199483)
                      ·
                        rfl

theorem cell23_3552581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 3, 6].length) (baseStart_3552581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3552581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3552581 prefixEnd_3552581 := by exact prefixLift 3552581
  have htrace : WordTrace (prefixWord ++ tailWord_3552581) baseStart_3552581 baseEnd_3552581 := by
    simpa [prefixWord, tailWord_3552581, baseEnd_3552581] using wordTrace_append hprefix tailTrace_3552581
  have hstable : (prefixWord ++ tailWord_3552581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552581).length < 2 ^ (prefixWord ++ tailWord_3552581).sum := by decide
  have hdescent : baseEnd_3552581 < baseStart_3552581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552642 : List Nat := [3, 4, 2, 1, 1, 1, 1, 4, 6]
def baseStart_3552642 : Nat := 118140960795 + 3552642 * 2 ^ 59
def prefixEnd_3552642 : Nat := 4983230072969 + 3 ^ 40 * 3552642 * 2
def baseEnd_3552642 : Nat := 202690326594488278392967

theorem tailTrace_3552642 : CollatzResearch.WordTrace tailWord_3552642 prefixEnd_3552642 202690326594488278392967 := by
  unfold tailWord_3552642
  simp only [CollatzResearch.WordTrace]
  refine ⟨32393874698848062948359045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86383665863594834528957453 32393874698848062948359045)
  ·
    refine ⟨6073851506034011802817321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32393874698848062948359045 6073851506034011802817321)
    ·
      refine ⟨4555388629525508852112991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6073851506034011802817321 4555388629525508852112991)
      ·
        refine ⟨6833082944288263278169487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4555388629525508852112991 6833082944288263278169487)
        ·
          refine ⟨10249624416432394917254231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6833082944288263278169487 10249624416432394917254231)
          ·
            refine ⟨15374436624648592375881347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10249624416432394917254231 15374436624648592375881347)
            ·
              refine ⟨23061654936972888563822021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15374436624648592375881347 23061654936972888563822021)
              ·
                refine ⟨4324060300682416605716629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23061654936972888563822021 4324060300682416605716629)
                ·
                  refine ⟨202690326594488278392967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4324060300682416605716629 202690326594488278392967)
                  ·
                    rfl

theorem cell23_3552642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_3552642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3552642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3552642 prefixEnd_3552642 := by exact prefixLift 3552642
  have htrace : WordTrace (prefixWord ++ tailWord_3552642) baseStart_3552642 baseEnd_3552642 := by
    simpa [prefixWord, tailWord_3552642, baseEnd_3552642] using wordTrace_append hprefix tailTrace_3552642
  have hstable : (prefixWord ++ tailWord_3552642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552642).length < 2 ^ (prefixWord ++ tailWord_3552642).sum := by decide
  have hdescent : baseEnd_3552642 < baseStart_3552642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552675 : List Nat := [1, 1, 1, 4, 1, 3, 2, 4, 1, 1, 4]
def baseStart_3552675 : Nat := 118140960795 + 3552675 * 2 ^ 59
def prefixEnd_3552675 : Nat := 4983230072969 + 3 ^ 40 * 3552675 * 2
def baseEnd_3552675 : Nat := 1824229884211992876424051

theorem tailTrace_3552675 : CollatzResearch.WordTrace tailWord_3552675 prefixEnd_3552675 1824229884211992876424051 := by
  unfold tailWord_3552675
  simp only [CollatzResearch.WordTrace]
  refine ⟨129576702404272698429387479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86384468269515132286258319 129576702404272698429387479)
  ·
    refine ⟨194365053606409047644081219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129576702404272698429387479 194365053606409047644081219)
    ·
      refine ⟨291547580409613571466121829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194365053606409047644081219 291547580409613571466121829)
      ·
        refine ⟨54665171326802544649897843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 291547580409613571466121829 54665171326802544649897843)
        ·
          refine ⟨81997756990203816974846765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54665171326802544649897843 81997756990203816974846765)
          ·
            refine ⟨30749158871326431365567537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81997756990203816974846765 30749158871326431365567537)
            ·
              refine ⟨23061869153494823524175653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30749158871326431365567537 23061869153494823524175653)
              ·
                refine ⟨4324100466280279410782935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23061869153494823524175653 4324100466280279410782935)
                ·
                  refine ⟨6486150699420419116174403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4324100466280279410782935 6486150699420419116174403)
                  ·
                    refine ⟨9729226049130628674261605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6486150699420419116174403 9729226049130628674261605)
                    ·
                      refine ⟨1824229884211992876424051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9729226049130628674261605 1824229884211992876424051)
                      ·
                        rfl

theorem cell23_3552675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 4, 1, 1, 4].length) (baseStart_3552675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3552675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3552675 prefixEnd_3552675 := by exact prefixLift 3552675
  have htrace : WordTrace (prefixWord ++ tailWord_3552675) baseStart_3552675 baseEnd_3552675 := by
    simpa [prefixWord, tailWord_3552675, baseEnd_3552675] using wordTrace_append hprefix tailTrace_3552675
  have hstable : (prefixWord ++ tailWord_3552675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552675).length < 2 ^ (prefixWord ++ tailWord_3552675).sum := by decide
  have hdescent : baseEnd_3552675 < baseStart_3552675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552688 : List Nat := [2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 4]
def baseStart_3552688 : Nat := 118140960795 + 3552688 * 2 ^ 59
def prefixEnd_3552688 : Nat := 4983230072969 + 3 ^ 40 * 3552688 * 2
def baseEnd_3552688 : Nat := 1824236559460501325561491

theorem tailTrace_3552688 : CollatzResearch.WordTrace tailWord_3552688 prefixEnd_3552688 1824236559460501325561491 := by
  unfold tailWord_3552688
  simp only [CollatzResearch.WordTrace]
  refine ⟨64788588276612800824805359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86384784368817067766407145 64788588276612800824805359)
  ·
    refine ⟨97182882414919201237208039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64788588276612800824805359 97182882414919201237208039)
    ·
      refine ⟨145774323622378801855812059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97182882414919201237208039 145774323622378801855812059)
      ·
        refine ⟨218661485433568202783718089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145774323622378801855812059 218661485433568202783718089)
        ·
          refine ⟨163996114075176152087788567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218661485433568202783718089 163996114075176152087788567)
          ·
            refine ⟨245994171112764228131682851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163996114075176152087788567 245994171112764228131682851)
            ·
              refine ⟨368991256669146342197524277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245994171112764228131682851 368991256669146342197524277)
              ·
                refine ⟨34592930312732469581017901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 368991256669146342197524277 34592930312732469581017901)
                ·
                  refine ⟨12972348867274676092881713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34592930312732469581017901 12972348867274676092881713)
                  ·
                    refine ⟨9729261650456007069661285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12972348867274676092881713 9729261650456007069661285)
                    ·
                      refine ⟨1824236559460501325561491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9729261650456007069661285 1824236559460501325561491)
                      ·
                        rfl

theorem cell23_3552688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 4].length) (baseStart_3552688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3552688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3552688 prefixEnd_3552688 := by exact prefixLift 3552688
  have htrace : WordTrace (prefixWord ++ tailWord_3552688) baseStart_3552688 baseEnd_3552688 := by
    simpa [prefixWord, tailWord_3552688, baseEnd_3552688] using wordTrace_append hprefix tailTrace_3552688
  have hstable : (prefixWord ++ tailWord_3552688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552688).length < 2 ^ (prefixWord ++ tailWord_3552688).sum := by decide
  have hdescent : baseEnd_3552688 < baseStart_3552688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552726 : List Nat := [5, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2]
def baseStart_3552726 : Nat := 118140960795 + 3552726 * 2 ^ 59
def prefixEnd_3552726 : Nat := 4983230072969 + 3 ^ 40 * 3552726 * 2
def baseEnd_3552726 : Nat := 1824256071725372176886317

theorem tailTrace_3552726 : CollatzResearch.WordTrace tailWord_3552726 prefixEnd_3552726 1824256071725372176886317 := by
  unfold tailWord_3552726
  simp only [CollatzResearch.WordTrace]
  refine ⟨8098660157942995883718377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86385708351391956092996021 8098660157942995883718377)
  ·
    refine ⟨6073995118457246912788783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8098660157942995883718377 6073995118457246912788783)
    ·
      refine ⟨9110992677685870369183175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6073995118457246912788783 9110992677685870369183175)
      ·
        refine ⟨13666489016528805553774763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9110992677685870369183175 13666489016528805553774763)
        ·
          refine ⟨20499733524793208330662145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13666489016528805553774763 20499733524793208330662145)
          ·
            refine ⟨15374800143594906247996609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20499733524793208330662145 15374800143594906247996609)
            ·
              refine ⟨11531100107696179685997457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15374800143594906247996609 11531100107696179685997457)
              ·
                refine ⟨8648325080772134764498093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11531100107696179685997457 8648325080772134764498093)
                ·
                  refine ⟨3243121905289550536686785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8648325080772134764498093 3243121905289550536686785)
                  ·
                    refine ⟨2432341428967162902515089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3243121905289550536686785 2432341428967162902515089)
                    ·
                      refine ⟨1824256071725372176886317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2432341428967162902515089 1824256071725372176886317)
                      ·
                        rfl

theorem cell23_3552726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_3552726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3552726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3552726 prefixEnd_3552726 := by exact prefixLift 3552726
  have htrace : WordTrace (prefixWord ++ tailWord_3552726) baseStart_3552726 baseEnd_3552726 := by
    simpa [prefixWord, tailWord_3552726, baseEnd_3552726] using wordTrace_append hprefix tailTrace_3552726
  have hstable : (prefixWord ++ tailWord_3552726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552726).length < 2 ^ (prefixWord ++ tailWord_3552726).sum := by decide
  have hdescent : baseEnd_3552726 < baseStart_3552726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552728 : List Nat := [2, 1, 2, 2, 2, 1, 2, 2, 2, 7]
def baseStart_3552728 : Nat := 118140960795 + 3552728 * 2 ^ 59
def prefixEnd_3552728 : Nat := 4983230072969 + 3 ^ 40 * 3552728 * 2
def baseEnd_3552728 : Nat := 608085699562227056353769

theorem tailTrace_3552728 : CollatzResearch.WordTrace tailWord_3552728 prefixEnd_3552728 608085699562227056353769 := by
  unfold tailWord_3552728
  simp only [CollatzResearch.WordTrace]
  refine ⟨64789317736540344240533419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86385756982053792320711225 64789317736540344240533419)
  ·
    refine ⟨97183976604810516360800129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64789317736540344240533419 97183976604810516360800129)
    ·
      refine ⟨72887982453607887270600097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97183976604810516360800129 72887982453607887270600097)
      ·
        refine ⟨54665986840205915452950073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72887982453607887270600097 54665986840205915452950073)
        ·
          refine ⟨40999490130154436589712555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54665986840205915452950073 40999490130154436589712555)
          ·
            refine ⟨61499235195231654884568833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40999490130154436589712555 61499235195231654884568833)
            ·
              refine ⟨46124426396423741163426625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61499235195231654884568833 46124426396423741163426625)
              ·
                refine ⟨34593319797317805872569969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46124426396423741163426625 34593319797317805872569969)
                ·
                  refine ⟨25944989847988354404427477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34593319797317805872569969 25944989847988354404427477)
                  ·
                    refine ⟨608085699562227056353769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25944989847988354404427477 608085699562227056353769)
                    ·
                      rfl

theorem cell23_3552728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 7].length) (baseStart_3552728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3552728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3552728 prefixEnd_3552728 := by exact prefixLift 3552728
  have htrace : WordTrace (prefixWord ++ tailWord_3552728) baseStart_3552728 baseEnd_3552728 := by
    simpa [prefixWord, tailWord_3552728, baseEnd_3552728] using wordTrace_append hprefix tailTrace_3552728
  have hstable : (prefixWord ++ tailWord_3552728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552728).length < 2 ^ (prefixWord ++ tailWord_3552728).sum := by decide
  have hdescent : baseEnd_3552728 < baseStart_3552728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552743 : List Nat := [1, 1, 5, 2, 1, 4, 1, 3, 1, 2, 2]
def baseStart_3552743 : Nat := 118140960795 + 3552743 * 2 ^ 59
def prefixEnd_3552743 : Nat := 4983230072969 + 3 ^ 40 * 3552743 * 2
def baseEnd_3552743 : Nat := 1824264800896498610373739

theorem tailTrace_3552743 : CollatzResearch.WordTrace tailWord_3552743 prefixEnd_3552743 1824264800896498610373739 := by
  unfold tailWord_3552743
  simp only [CollatzResearch.WordTrace]
  refine ⟨129579182568026346042862883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86386121712017564028575255 129579182568026346042862883)
  ·
    refine ⟨194368773852039519064294325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129579182568026346042862883 194368773852039519064294325)
    ·
      refine ⟨18222072548628704912277593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 194368773852039519064294325 18222072548628704912277593)
      ·
        refine ⟨13666554411471528684208195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18222072548628704912277593 13666554411471528684208195)
        ·
          refine ⟨20499831617207293026312293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13666554411471528684208195 20499831617207293026312293)
          ·
            refine ⟨3843718428226367442433555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20499831617207293026312293 3843718428226367442433555)
            ·
              refine ⟨5765577642339551163650333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3843718428226367442433555 5765577642339551163650333)
              ·
                refine ⟨2162091615877331686368875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5765577642339551163650333 2162091615877331686368875)
                ·
                  refine ⟨3243137423815997529553313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2162091615877331686368875 3243137423815997529553313)
                  ·
                    refine ⟨2432353067861998147164985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3243137423815997529553313 2432353067861998147164985)
                    ·
                      refine ⟨1824264800896498610373739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2432353067861998147164985 1824264800896498610373739)
                      ·
                        rfl

theorem cell23_3552743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_3552743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3552743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3552743 prefixEnd_3552743 := by exact prefixLift 3552743
  have htrace : WordTrace (prefixWord ++ tailWord_3552743) baseStart_3552743 baseEnd_3552743 := by
    simpa [prefixWord, tailWord_3552743, baseEnd_3552743] using wordTrace_append hprefix tailTrace_3552743
  have hstable : (prefixWord ++ tailWord_3552743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552743).length < 2 ^ (prefixWord ++ tailWord_3552743).sum := by decide
  have hdescent : baseEnd_3552743 < baseStart_3552743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552842 : List Nat := [3, 1, 2, 1, 1, 3, 1, 2, 2, 5, 2]
def baseStart_3552842 : Nat := 118140960795 + 3552842 * 2 ^ 59
def prefixEnd_3552842 : Nat := 4983230072969 + 3 ^ 40 * 3552842 * 2
def baseEnd_3552842 : Nat := 1824315635481293723035783

theorem tailTrace_3552842 : CollatzResearch.WordTrace tailWord_3552842 prefixEnd_3552842 1824315635481293723035783 := by
  unfold tailWord_3552842
  simp only [CollatzResearch.WordTrace]
  refine ⟨32395698348666921487679195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86388528929778457300477853 32395698348666921487679195)
  ·
    refine ⟨48593547523000382231518793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32395698348666921487679195 48593547523000382231518793)
    ·
      refine ⟨36445160642250286673639095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48593547523000382231518793 36445160642250286673639095)
      ·
        refine ⟨54667740963375430010458643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36445160642250286673639095 54667740963375430010458643)
        ·
          refine ⟨82001611445063145015687965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54667740963375430010458643 82001611445063145015687965)
          ·
            refine ⟨30750604291898679380882987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82001611445063145015687965 30750604291898679380882987)
            ·
              refine ⟨46125906437848019071324481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30750604291898679380882987 46125906437848019071324481)
              ·
                refine ⟨34594429828386014303493361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46125906437848019071324481 34594429828386014303493361)
                ·
                  refine ⟨25945822371289510727620021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34594429828386014303493361 25945822371289510727620021)
                  ·
                    refine ⟨2432420847308391630714377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25945822371289510727620021 2432420847308391630714377)
                    ·
                      refine ⟨1824315635481293723035783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2432420847308391630714377 1824315635481293723035783)
                      ·
                        rfl

theorem cell23_3552842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 2, 5, 2].length) (baseStart_3552842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3552842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3552842 prefixEnd_3552842 := by exact prefixLift 3552842
  have htrace : WordTrace (prefixWord ++ tailWord_3552842) baseStart_3552842 baseEnd_3552842 := by
    simpa [prefixWord, tailWord_3552842, baseEnd_3552842] using wordTrace_append hprefix tailTrace_3552842
  have hstable : (prefixWord ++ tailWord_3552842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552842).length < 2 ^ (prefixWord ++ tailWord_3552842).sum := by decide
  have hdescent : baseEnd_3552842 < baseStart_3552842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552854 : List Nat := [5, 2, 2, 2, 2, 1, 2, 1, 1, 3, 2]
def baseStart_3552854 : Nat := 118140960795 + 3552854 * 2 ^ 59
def prefixEnd_3552854 : Nat := 4983230072969 + 3 ^ 40 * 3552854 * 2
def baseEnd_3552854 : Nat := 1824321797249147676085729

theorem tailTrace_3552854 : CollatzResearch.WordTrace tailWord_3552854 prefixEnd_3552854 1824321797249147676085729 := by
  unfold tailWord_3552854
  simp only [CollatzResearch.WordTrace]
  refine ⟨8098951941914013250009601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86388820713749474666769077 8098951941914013250009601)
  ·
    refine ⟨6074213956435509937507201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8098951941914013250009601 6074213956435509937507201)
    ·
      refine ⟨4555660467326632453130401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6074213956435509937507201 4555660467326632453130401)
      ·
        refine ⟨3416745350494974339847801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4555660467326632453130401 3416745350494974339847801)
        ·
          refine ⟨2562559012871230754885851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3416745350494974339847801 2562559012871230754885851)
          ·
            refine ⟨3843838519306846132328777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2562559012871230754885851 3843838519306846132328777)
            ·
              refine ⟨2882878889480134599246583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3843838519306846132328777 2882878889480134599246583)
              ·
                refine ⟨4324318334220201898869875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2882878889480134599246583 4324318334220201898869875)
                ·
                  refine ⟨6486477501330302848304813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4324318334220201898869875 6486477501330302848304813)
                  ·
                    refine ⟨2432429062998863568114305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6486477501330302848304813 2432429062998863568114305)
                    ·
                      refine ⟨1824321797249147676085729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2432429062998863568114305 1824321797249147676085729)
                      ·
                        rfl

theorem cell23_3552854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_3552854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3552854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3552854 prefixEnd_3552854 := by exact prefixLift 3552854
  have htrace : WordTrace (prefixWord ++ tailWord_3552854) baseStart_3552854 baseEnd_3552854 := by
    simpa [prefixWord, tailWord_3552854, baseEnd_3552854] using wordTrace_append hprefix tailTrace_3552854
  have hstable : (prefixWord ++ tailWord_3552854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552854).length < 2 ^ (prefixWord ++ tailWord_3552854).sum := by decide
  have hdescent : baseEnd_3552854 < baseStart_3552854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552926 : List Nat := [4, 3, 1, 1, 1, 3, 1, 2, 2, 2, 3]
def baseStart_3552926 : Nat := 118140960795 + 3552926 * 2 ^ 59
def prefixEnd_3552926 : Nat := 4983230072969 + 3 ^ 40 * 3552926 * 2
def baseEnd_3552926 : Nat := 1824358767856271394385397

theorem tailTrace_3552926 : CollatzResearch.WordTrace tailWord_3552926 prefixEnd_3552926 1824358767856271394385397 := by
  unfold tailWord_3552926
  simp only [CollatzResearch.WordTrace]
  refine ⟨16198232140795421037096829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86390571417575578864516421 16198232140795421037096829)
  ·
    refine ⟨6074337052798282888911311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16198232140795421037096829 6074337052798282888911311)
    ·
      refine ⟨9111505579197424333366967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6074337052798282888911311 9111505579197424333366967)
      ·
        refine ⟨13667258368796136500050451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9111505579197424333366967 13667258368796136500050451)
        ·
          refine ⟨20500887553194204750075677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13667258368796136500050451 20500887553194204750075677)
          ·
            refine ⟨7687832832447826781278379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20500887553194204750075677 7687832832447826781278379)
            ·
              refine ⟨11531749248671740171917569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7687832832447826781278379 11531749248671740171917569)
              ·
                refine ⟨8648811936503805128938177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11531749248671740171917569 8648811936503805128938177)
                ·
                  refine ⟨6486608952377853846703633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8648811936503805128938177 6486608952377853846703633)
                  ·
                    refine ⟨4864956714283390385027725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6486608952377853846703633 4864956714283390385027725)
                    ·
                      refine ⟨1824358767856271394385397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4864956714283390385027725 1824358767856271394385397)
                      ·
                        rfl

theorem cell23_3552926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_3552926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3552926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3552926 prefixEnd_3552926 := by exact prefixLift 3552926
  have htrace : WordTrace (prefixWord ++ tailWord_3552926) baseStart_3552926 baseEnd_3552926 := by
    simpa [prefixWord, tailWord_3552926, baseEnd_3552926] using wordTrace_append hprefix tailTrace_3552926
  have hstable : (prefixWord ++ tailWord_3552926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552926).length < 2 ^ (prefixWord ++ tailWord_3552926).sum := by decide
  have hdescent : baseEnd_3552926 < baseStart_3552926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552955 : List Nat := [1, 1, 1, 1, 1, 2, 3, 2, 5, 6]
def baseStart_3552955 : Nat := 118140960795 + 3552955 * 2 ^ 59
def prefixEnd_3552955 : Nat := 4983230072969 + 3 ^ 40 * 3552955 * 2
def baseEnd_3552955 : Nat := 608124552931750593640921

theorem tailTrace_3552955 : CollatzResearch.WordTrace tailWord_3552955 prefixEnd_3552955 608124552931750593640921 := by
  unfold tailWord_3552955
  simp only [CollatzResearch.WordTrace]
  refine ⟨129586914843258306249580319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86391276562172204166386879 129586914843258306249580319)
  ·
    refine ⟨194380372264887459374370479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129586914843258306249580319 194380372264887459374370479)
    ·
      refine ⟨291570558397331189061555719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194380372264887459374370479 291570558397331189061555719)
      ·
        refine ⟨437355837595996783592333579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291570558397331189061555719 437355837595996783592333579)
        ·
          refine ⟨656033756393995175388500369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437355837595996783592333579 656033756393995175388500369)
          ·
            refine ⟨492025317295496381541375277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 656033756393995175388500369 492025317295496381541375277)
            ·
              refine ⟨184509493985811143078015729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 492025317295496381541375277 184509493985811143078015729)
              ·
                refine ⟨138382120489358357308511797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184509493985811143078015729 138382120489358357308511797)
                ·
                  refine ⟨12973323795877345997672981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 138382120489358357308511797 12973323795877345997672981)
                  ·
                    refine ⟨608124552931750593640921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12973323795877345997672981 608124552931750593640921)
                    ·
                      rfl

theorem cell23_3552955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5, 6].length) (baseStart_3552955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3552955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3552955 prefixEnd_3552955 := by exact prefixLift 3552955
  have htrace : WordTrace (prefixWord ++ tailWord_3552955) baseStart_3552955 baseEnd_3552955 := by
    simpa [prefixWord, tailWord_3552955, baseEnd_3552955] using wordTrace_append hprefix tailTrace_3552955
  have hstable : (prefixWord ++ tailWord_3552955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552955).length < 2 ^ (prefixWord ++ tailWord_3552955).sum := by decide
  have hdescent : baseEnd_3552955 < baseStart_3552955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552985 : List Nat := [1, 2, 1, 2, 3, 14]
def baseStart_3552985 : Nat := 118140960795 + 3552985 * 2 ^ 59
def prefixEnd_3552985 : Nat := 4983230072969 + 3 ^ 40 * 3552985 * 2
def baseEnd_3552985 : Nat := 7507773922695006845875

theorem tailTrace_3552985 : CollatzResearch.WordTrace tailWord_3552985 prefixEnd_3552985 7507773922695006845875 := by
  unfold tailWord_3552985
  simp only [CollatzResearch.WordTrace]
  refine ⟨129588009033149621373172409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86392006022099747582114939 129588009033149621373172409)
  ·
    refine ⟨97191006774862216029879307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129588009033149621373172409 97191006774862216029879307)
    ·
      refine ⟨145786510162293324044818961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97191006774862216029879307 145786510162293324044818961)
      ·
        refine ⟨109339882621719993033614221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145786510162293324044818961 109339882621719993033614221)
        ·
          refine ⟨41002455983144997387605333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109339882621719993033614221 41002455983144997387605333)
          ·
            refine ⟨7507773922695006845875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 41002455983144997387605333 7507773922695006845875)
            ·
              rfl

theorem cell23_3552985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 14].length) (baseStart_3552985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3552985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3552985 prefixEnd_3552985 := by exact prefixLift 3552985
  have htrace : WordTrace (prefixWord ++ tailWord_3552985) baseStart_3552985 baseEnd_3552985 := by
    simpa [prefixWord, tailWord_3552985, baseEnd_3552985] using wordTrace_append hprefix tailTrace_3552985
  have hstable : (prefixWord ++ tailWord_3552985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552985).length < 2 ^ (prefixWord ++ tailWord_3552985).sum := by decide
  have hdescent : baseEnd_3552985 < baseStart_3552985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3552996 : List Nat := [2, 3, 1, 1, 1, 3, 2, 3, 3, 2, 2]
def baseStart_3552996 : Nat := 118140960795 + 3552996 * 2 ^ 59
def prefixEnd_3552996 : Nat := 4983230072969 + 3 ^ 40 * 3552996 * 2
def baseEnd_3552996 : Nat := 1824394711502086120510075

theorem tailTrace_3552996 : CollatzResearch.WordTrace tailWord_3552996 prefixEnd_3552996 1824394711502086120510075 := by
  unfold tailWord_3552996
  simp only [CollatzResearch.WordTrace]
  refine ⟨64794205118054885125911421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86392273490739846834548561 64794205118054885125911421)
  ·
    refine ⟨24297826919270581922216783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64794205118054885125911421 24297826919270581922216783)
    ·
      refine ⟨36446740378905872883325175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24297826919270581922216783 36446740378905872883325175)
      ·
        refine ⟨54670110568358809324987763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36446740378905872883325175 54670110568358809324987763)
        ·
          refine ⟨82005165852538213987481645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54670110568358809324987763 82005165852538213987481645)
          ·
            refine ⟨30751937194701830245305617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82005165852538213987481645 30751937194701830245305617)
            ·
              refine ⟨23063952896026372683979213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30751937194701830245305617 23063952896026372683979213)
              ·
                refine ⟨8648982336009889756492205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23063952896026372683979213 8648982336009889756492205)
                ·
                  refine ⟨3243368376003708658684577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8648982336009889756492205 3243368376003708658684577)
                  ·
                    refine ⟨2432526282002781494013433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3243368376003708658684577 2432526282002781494013433)
                    ·
                      refine ⟨1824394711502086120510075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2432526282002781494013433 1824394711502086120510075)
                      ·
                        rfl

theorem cell23_3552996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3, 3, 2, 2].length) (baseStart_3552996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3552996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3552996 prefixEnd_3552996 := by exact prefixLift 3552996
  have htrace : WordTrace (prefixWord ++ tailWord_3552996) baseStart_3552996 baseEnd_3552996 := by
    simpa [prefixWord, tailWord_3552996, baseEnd_3552996] using wordTrace_append hprefix tailTrace_3552996
  have hstable : (prefixWord ++ tailWord_3552996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3552996).length < 2 ^ (prefixWord ++ tailWord_3552996).sum := by decide
  have hdescent : baseEnd_3552996 < baseStart_3552996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3552996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553002 : List Nat := [3, 1, 3, 1, 1, 1, 5, 8]
def baseStart_3553002 : Nat := 118140960795 + 3553002 * 2 ^ 59
def prefixEnd_3553002 : Nat := 4983230072969 + 3 ^ 40 * 3553002 * 2
def baseEnd_3553002 : Nat := 67570288606889373964261

theorem tailTrace_3553002 : CollatzResearch.WordTrace tailWord_3553002 prefixEnd_3553002 67570288606889373964261 := by
  unfold tailWord_3553002
  simp only [CollatzResearch.WordTrace]
  refine ⟨32397157268522008319135315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86392419382725355517694173 32397157268522008319135315)
  ·
    refine ⟨48595735902783012478702973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32397157268522008319135315 48595735902783012478702973)
    ·
      refine ⟨18223400963543629679513615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48595735902783012478702973 18223400963543629679513615)
      ·
        refine ⟨27335101445315444519270423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18223400963543629679513615 27335101445315444519270423)
        ·
          refine ⟨41002652167973166778905635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27335101445315444519270423 41002652167973166778905635)
          ·
            refine ⟨61503978251959750168358453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41002652167973166778905635 61503978251959750168358453)
            ·
              refine ⟨5765997961121226578283605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61503978251959750168358453 5765997961121226578283605)
              ·
                refine ⟨67570288606889373964261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5765997961121226578283605 67570288606889373964261)
                ·
                  rfl

theorem cell23_3553002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 8].length) (baseStart_3553002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3553002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3553002 prefixEnd_3553002 := by exact prefixLift 3553002
  have htrace : WordTrace (prefixWord ++ tailWord_3553002) baseStart_3553002 baseEnd_3553002 := by
    simpa [prefixWord, tailWord_3553002, baseEnd_3553002] using wordTrace_append hprefix tailTrace_3553002
  have hstable : (prefixWord ++ tailWord_3553002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553002).length < 2 ^ (prefixWord ++ tailWord_3553002).sum := by decide
  have hdescent : baseEnd_3553002 < baseStart_3553002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553009 : List Nat := [1, 2, 2, 2, 2, 4, 2, 1, 1, 2, 4]
def baseStart_3553009 : Nat := 118140960795 + 3553009 * 2 ^ 59
def prefixEnd_3553009 : Nat := 4983230072969 + 3 ^ 40 * 3553009 * 2
def baseEnd_3553009 : Nat := 1824401386750594569647515

theorem tailTrace_3553009 : CollatzResearch.WordTrace tailWord_3553009 prefixEnd_3553009 1824401386750594569647515 := by
  unfold tailWord_3553009
  simp only [CollatzResearch.WordTrace]
  refine ⟨129588884385062673472046081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86392589590041782314697387 129588884385062673472046081)
  ·
    refine ⟨97191663288797005104034561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129588884385062673472046081 97191663288797005104034561)
    ·
      refine ⟨72893747466597753828025921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97191663288797005104034561 72893747466597753828025921)
      ·
        refine ⟨54670310599948315371019441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72893747466597753828025921 54670310599948315371019441)
        ·
          refine ⟨41002732949961236528264581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54670310599948315371019441 41002732949961236528264581)
          ·
            refine ⟨7688012428117731849049609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41002732949961236528264581 7688012428117731849049609)
            ·
              refine ⟨5766009321088298886787207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7688012428117731849049609 5766009321088298886787207)
              ·
                refine ⟨8649013981632448330180811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5766009321088298886787207 8649013981632448330180811)
                ·
                  refine ⟨12973520972448672495271217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8649013981632448330180811 12973520972448672495271217)
                  ·
                    refine ⟨9730140729336504371453413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12973520972448672495271217 9730140729336504371453413)
                    ·
                      refine ⟨1824401386750594569647515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9730140729336504371453413 1824401386750594569647515)
                      ·
                        rfl

theorem cell23_3553009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 1, 1, 2, 4].length) (baseStart_3553009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3553009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3553009 prefixEnd_3553009 := by exact prefixLift 3553009
  have htrace : WordTrace (prefixWord ++ tailWord_3553009) baseStart_3553009 baseEnd_3553009 := by
    simpa [prefixWord, tailWord_3553009, baseEnd_3553009] using wordTrace_append hprefix tailTrace_3553009
  have hstable : (prefixWord ++ tailWord_3553009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553009).length < 2 ^ (prefixWord ++ tailWord_3553009).sum := by decide
  have hdescent : baseEnd_3553009 < baseStart_3553009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553039 : List Nat := [1, 1, 2, 1, 1, 1, 4, 2, 5, 3, 2]
def baseStart_3553039 : Nat := 118140960795 + 3553039 * 2 ^ 59
def prefixEnd_3553039 : Nat := 4983230072969 + 3 ^ 40 * 3553039 * 2
def baseEnd_3553039 : Nat := 1824416791170229452272377

theorem tailTrace_3553039 : CollatzResearch.WordTrace tailWord_3553039 prefixEnd_3553039 1824416791170229452272377 := by
  unfold tailWord_3553039
  simp only [CollatzResearch.WordTrace]
  refine ⟨129589978574953988595638171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86393319049969325730425447 129589978574953988595638171)
  ·
    refine ⟨194384967862430982893457257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129589978574953988595638171 194384967862430982893457257)
    ·
      refine ⟨145788725896823237170092943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194384967862430982893457257 145788725896823237170092943)
      ·
        refine ⟨218683088845234855755139415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145788725896823237170092943 218683088845234855755139415)
        ·
          refine ⟨328024633267852283632709123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218683088845234855755139415 328024633267852283632709123)
          ·
            refine ⟨492036949901778425449063685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328024633267852283632709123 492036949901778425449063685)
            ·
              refine ⟨92256928106583454771699441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 492036949901778425449063685 92256928106583454771699441)
              ·
                refine ⟨69192696079937591078774581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92256928106583454771699441 69192696079937591078774581)
                ·
                  refine ⟨6486815257494149163635117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69192696079937591078774581 6486815257494149163635117)
                  ·
                    refine ⟨2432555721560305936363169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6486815257494149163635117 2432555721560305936363169)
                    ·
                      refine ⟨1824416791170229452272377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2432555721560305936363169 1824416791170229452272377)
                      ·
                        rfl

theorem cell23_3553039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 5, 3, 2].length) (baseStart_3553039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3553039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3553039 prefixEnd_3553039 := by exact prefixLift 3553039
  have htrace : WordTrace (prefixWord ++ tailWord_3553039) baseStart_3553039 baseEnd_3553039 := by
    simpa [prefixWord, tailWord_3553039, baseEnd_3553039] using wordTrace_append hprefix tailTrace_3553039
  have hstable : (prefixWord ++ tailWord_3553039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553039).length < 2 ^ (prefixWord ++ tailWord_3553039).sum := by decide
  have hdescent : baseEnd_3553039 < baseStart_3553039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553073 : List Nat := [1, 2, 2, 3, 2, 3, 2, 2, 1, 3, 2]
def baseStart_3553073 : Nat := 118140960795 + 3553073 * 2 ^ 59
def prefixEnd_3553073 : Nat := 4983230072969 + 3 ^ 40 * 3553073 * 2
def baseEnd_3553073 : Nat := 1824434249512482319247221

theorem tailTrace_3553073 : CollatzResearch.WordTrace tailWord_3553073 prefixEnd_3553073 1824434249512482319247221 := by
  unfold tailWord_3553073
  simp only [CollatzResearch.WordTrace]
  refine ⟨129591218656830812402375873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86394145771220541601583915 129591218656830812402375873)
  ·
    refine ⟨97193413992623109301781905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129591218656830812402375873 97193413992623109301781905)
    ·
      refine ⟨72895060494467331976336429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97193413992623109301781905 72895060494467331976336429)
      ·
        refine ⟨27335647685425249491126161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72895060494467331976336429 27335647685425249491126161)
        ·
          refine ⟨20501735764068937118344621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27335647685425249491126161 20501735764068937118344621)
          ·
            refine ⟨7688150911525851419379233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20501735764068937118344621 7688150911525851419379233)
            ·
              refine ⟨5766113183644388564534425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7688150911525851419379233 5766113183644388564534425)
              ·
                refine ⟨4324584887733291423400819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5766113183644388564534425 4324584887733291423400819)
                ·
                  refine ⟨6486877331599937135101229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4324584887733291423400819 6486877331599937135101229)
                  ·
                    refine ⟨2432578999349976425662961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6486877331599937135101229 2432578999349976425662961)
                    ·
                      refine ⟨1824434249512482319247221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2432578999349976425662961 1824434249512482319247221)
                      ·
                        rfl

theorem cell23_3553073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 2, 1, 3, 2].length) (baseStart_3553073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3553073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3553073 prefixEnd_3553073 := by exact prefixLift 3553073
  have htrace : WordTrace (prefixWord ++ tailWord_3553073) baseStart_3553073 baseEnd_3553073 := by
    simpa [prefixWord, tailWord_3553073, baseEnd_3553073] using wordTrace_append hprefix tailTrace_3553073
  have hstable : (prefixWord ++ tailWord_3553073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553073).length < 2 ^ (prefixWord ++ tailWord_3553073).sum := by decide
  have hdescent : baseEnd_3553073 < baseStart_3553073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553109 : List Nat := [1, 3, 2, 2, 2, 2, 3, 1, 7]
def baseStart_3553109 : Nat := 118140960795 + 3553109 * 2 ^ 59
def prefixEnd_3553109 : Nat := 4983230072969 + 3 ^ 40 * 3553109 * 2
def baseEnd_3553109 : Nat := 202716970535116019821895

theorem tailTrace_3553109 : CollatzResearch.WordTrace tailWord_3553109 prefixEnd_3553109 202716970535116019821895 := by
  unfold tailWord_3553109
  simp only [CollatzResearch.WordTrace]
  refine ⟨129592531684700390550686381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86395021123133593700457587 129592531684700390550686381)
  ·
    refine ⟨48597199381762646456507393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129592531684700390550686381 48597199381762646456507393)
    ·
      refine ⟨36447899536321984842380545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48597199381762646456507393 36447899536321984842380545)
      ·
        refine ⟨27335924652241488631785409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36447899536321984842380545 27335924652241488631785409)
        ·
          refine ⟨20501943489181116473839057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27335924652241488631785409 20501943489181116473839057)
          ·
            refine ⟨15376457616885837355379293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20501943489181116473839057 15376457616885837355379293)
            ·
              refine ⟨5766171606332189008267235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15376457616885837355379293 5766171606332189008267235)
              ·
                refine ⟨8649257409498283512400853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5766171606332189008267235 8649257409498283512400853)
                ·
                  refine ⟨202716970535116019821895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8649257409498283512400853 202716970535116019821895)
                  ·
                    rfl

theorem cell23_3553109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 1, 7].length) (baseStart_3553109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3553109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3553109 prefixEnd_3553109 := by exact prefixLift 3553109
  have htrace : WordTrace (prefixWord ++ tailWord_3553109) baseStart_3553109 baseEnd_3553109 := by
    simpa [prefixWord, tailWord_3553109, baseEnd_3553109] using wordTrace_append hprefix tailTrace_3553109
  have hstable : (prefixWord ++ tailWord_3553109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553109).length < 2 ^ (prefixWord ++ tailWord_3553109).sum := by decide
  have hdescent : baseEnd_3553109 < baseStart_3553109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553120 : List Nat := [2, 1, 1, 3, 3, 2, 4, 1, 2, 2, 2]
def baseStart_3553120 : Nat := 118140960795 + 3553120 * 2 ^ 59
def prefixEnd_3553120 : Nat := 4983230072969 + 3 ^ 40 * 3553120 * 2
def baseEnd_3553120 : Nat := 1824458383103243635359505

theorem tailTrace_3553120 : CollatzResearch.WordTrace tailWord_3553120 prefixEnd_3553120 1824458383103243635359505 := by
  unfold tailWord_3553120
  simp only [CollatzResearch.WordTrace]
  refine ⟨64796466443830269714668407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86395288591773692952891209 64796466443830269714668407)
  ·
    refine ⟨97194699665745404572002611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64796466443830269714668407 97194699665745404572002611)
    ·
      refine ⟨145792049498618106858003917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97194699665745404572002611 145792049498618106858003917)
      ·
        refine ⟨54672018561981790071751469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145792049498618106858003917 54672018561981790071751469)
        ·
          refine ⟨20502006960743171276906801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54672018561981790071751469 20502006960743171276906801)
          ·
            refine ⟨15376505220557378457680101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20502006960743171276906801 15376505220557378457680101)
            ·
              refine ⟨2883094728854508460815019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15376505220557378457680101 2883094728854508460815019)
              ·
                refine ⟨4324642093281762691222529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2883094728854508460815019 4324642093281762691222529)
                ·
                  refine ⟨3243481569961322018416897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4324642093281762691222529 3243481569961322018416897)
                  ·
                    refine ⟨2432611177470991513812673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3243481569961322018416897 2432611177470991513812673)
                    ·
                      refine ⟨1824458383103243635359505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2432611177470991513812673 1824458383103243635359505)
                      ·
                        rfl

theorem cell23_3553120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4, 1, 2, 2, 2].length) (baseStart_3553120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3553120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3553120 prefixEnd_3553120 := by exact prefixLift 3553120
  have htrace : WordTrace (prefixWord ++ tailWord_3553120) baseStart_3553120 baseEnd_3553120 := by
    simpa [prefixWord, tailWord_3553120, baseEnd_3553120] using wordTrace_append hprefix tailTrace_3553120
  have hstable : (prefixWord ++ tailWord_3553120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553120).length < 2 ^ (prefixWord ++ tailWord_3553120).sum := by decide
  have hdescent : baseEnd_3553120 < baseStart_3553120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553160 : List Nat := [2, 1, 3, 3, 3, 2, 2, 2, 5]
def baseStart_3553160 : Nat := 118140960795 + 3553160 * 2 ^ 59
def prefixEnd_3553160 : Nat := 4983230072969 + 3 ^ 40 * 3553160 * 2
def baseEnd_3553160 : Nat := 202719880258824830984369

theorem tailTrace_3553160 : CollatzResearch.WordTrace tailWord_3553160 prefixEnd_3553160 202719880258824830984369 := by
  unfold tailWord_3553160
  simp only [CollatzResearch.WordTrace]
  refine ⟨64797195903757813130396467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86396261205010417507195289 64797195903757813130396467)
  ·
    refine ⟨97195793855636719695594701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64797195903757813130396467 97195793855636719695594701)
    ·
      refine ⟨36448422695863769885848013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97195793855636719695594701 36448422695863769885848013)
      ·
        refine ⟨13668158510948913707193005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36448422695863769885848013 13668158510948913707193005)
        ·
          refine ⟨5125559441605842640197377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13668158510948913707193005 5125559441605842640197377)
          ·
            refine ⟨3844169581204381980148033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5125559441605842640197377 3844169581204381980148033)
            ·
              refine ⟨2883127185903286485111025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3844169581204381980148033 2883127185903286485111025)
              ·
                refine ⟨2162345389427464863833269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2883127185903286485111025 2162345389427464863833269)
                ·
                  refine ⟨202719880258824830984369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2162345389427464863833269 202719880258824830984369)
                  ·
                    rfl

theorem cell23_3553160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2, 2, 5].length) (baseStart_3553160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3553160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3553160 prefixEnd_3553160 := by exact prefixLift 3553160
  have htrace : WordTrace (prefixWord ++ tailWord_3553160) baseStart_3553160 baseEnd_3553160 := by
    simpa [prefixWord, tailWord_3553160, baseEnd_3553160] using wordTrace_append hprefix tailTrace_3553160
  have hstable : (prefixWord ++ tailWord_3553160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553160).length < 2 ^ (prefixWord ++ tailWord_3553160).sum := by decide
  have hdescent : baseEnd_3553160 < baseStart_3553160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553203 : List Nat := [1, 1, 1, 2, 3, 1, 6, 3, 1, 4]
def baseStart_3553203 : Nat := 118140960795 + 3553203 * 2 ^ 59
def prefixEnd_3553203 : Nat := 4983230072969 + 3 ^ 40 * 3553203 * 2
def baseEnd_3553203 : Nat := 608167000665855603540541

theorem tailTrace_3553203 : CollatzResearch.WordTrace tailWord_3553203 prefixEnd_3553203 608167000665855603540541 := by
  unfold tailWord_3553203
  simp only [CollatzResearch.WordTrace]
  refine ⟨129595960146359844604608263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86397306764239896403072175 129595960146359844604608263)
  ·
    refine ⟨194393940219539766906912395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129595960146359844604608263 194393940219539766906912395)
    ·
      refine ⟨291590910329309650360368593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194393940219539766906912395 291590910329309650360368593)
      ·
        refine ⟨218693182746982237770276445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291590910329309650360368593 218693182746982237770276445)
        ·
          refine ⟨82009943530118339163853667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218693182746982237770276445 82009943530118339163853667)
          ·
            refine ⟨123014915295177508745780501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82009943530118339163853667 123014915295177508745780501)
            ·
              refine ⟨5766324154461445722458461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 123014915295177508745780501 5766324154461445722458461)
              ·
                refine ⟨2162371557923042145921923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5766324154461445722458461 2162371557923042145921923)
                ·
                  refine ⟨3243557336884563218882885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2162371557923042145921923 3243557336884563218882885)
                  ·
                    refine ⟨608167000665855603540541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3243557336884563218882885 608167000665855603540541)
                    ·
                      rfl

theorem cell23_3553203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 3, 1, 4].length) (baseStart_3553203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3553203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3553203 prefixEnd_3553203 := by exact prefixLift 3553203
  have htrace : WordTrace (prefixWord ++ tailWord_3553203) baseStart_3553203 baseEnd_3553203 := by
    simpa [prefixWord, tailWord_3553203, baseEnd_3553203] using wordTrace_append hprefix tailTrace_3553203
  have hstable : (prefixWord ++ tailWord_3553203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553203).length < 2 ^ (prefixWord ++ tailWord_3553203).sum := by decide
  have hdescent : baseEnd_3553203 < baseStart_3553203 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553259 : List Nat := [1, 1, 1, 1, 2, 3, 1, 6, 1, 6]
def baseStart_3553259 : Nat := 118140960795 + 3553259 * 2 ^ 59
def prefixEnd_3553259 : Nat := 4983230072969 + 3 ^ 40 * 3553259 * 2
def baseEnd_3553259 : Nat := 608176585638072863840455

theorem tailTrace_3553259 : CollatzResearch.WordTrace tailWord_3553259 prefixEnd_3553259 608176585638072863840455 := by
  unfold tailWord_3553259
  simp only [CollatzResearch.WordTrace]
  refine ⟨129598002634156966168646831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86398668422771310779097887 129598002634156966168646831)
  ·
    refine ⟨194397003951235449252970247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129598002634156966168646831 194397003951235449252970247)
    ·
      refine ⟨291595505926853173879455371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194397003951235449252970247 291595505926853173879455371)
      ·
        refine ⟨437393258890279760819183057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291595505926853173879455371 437393258890279760819183057)
        ·
          refine ⟨328044944167709820614387293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 437393258890279760819183057 328044944167709820614387293)
          ·
            refine ⟨123016854062891182730395235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 328044944167709820614387293 123016854062891182730395235)
            ·
              refine ⟨184525281094336774095592853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123016854062891182730395235 184525281094336774095592853)
              ·
                refine ⟨8649622551297036285730915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 184525281094336774095592853 8649622551297036285730915)
                ·
                  refine ⟨12974433826945554428596373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8649622551297036285730915 12974433826945554428596373)
                  ·
                    refine ⟨608176585638072863840455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12974433826945554428596373 608176585638072863840455)
                    ·
                      rfl

theorem cell23_3553259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6, 1, 6].length) (baseStart_3553259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3553259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3553259 prefixEnd_3553259 := by exact prefixLift 3553259
  have htrace : WordTrace (prefixWord ++ tailWord_3553259) baseStart_3553259 baseEnd_3553259 := by
    simpa [prefixWord, tailWord_3553259, baseEnd_3553259] using wordTrace_append hprefix tailTrace_3553259
  have hstable : (prefixWord ++ tailWord_3553259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553259).length < 2 ^ (prefixWord ++ tailWord_3553259).sum := by decide
  have hdescent : baseEnd_3553259 < baseStart_3553259 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553276 : List Nat := [2, 2, 2, 1, 2, 2, 1, 3, 4, 4]
def baseStart_3553276 : Nat := 118140960795 + 3553276 * 2 ^ 59
def prefixEnd_3553276 : Nat := 4983230072969 + 3 ^ 40 * 3553276 * 2
def baseEnd_3553276 : Nat := 608179495361781675002929

theorem tailTrace_3553276 : CollatzResearch.WordTrace tailWord_3553276 prefixEnd_3553276 608179495361781675002929 := by
  unfold tailWord_3553276
  simp only [CollatzResearch.WordTrace]
  refine ⟨64799311337547689036007841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86399081783396918714677121 64799311337547689036007841)
  ·
    refine ⟨48599483503160766777005881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64799311337547689036007841 48599483503160766777005881)
    ·
      refine ⟨36449612627370575082754411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48599483503160766777005881 36449612627370575082754411)
      ·
        refine ⟨54674418941055862624131617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36449612627370575082754411 54674418941055862624131617)
        ·
          refine ⟨41005814205791896968098713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54674418941055862624131617 41005814205791896968098713)
          ·
            refine ⟨30754360654343922726074035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41005814205791896968098713 30754360654343922726074035)
            ·
              refine ⟨46131540981515884089111053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30754360654343922726074035 46131540981515884089111053)
              ·
                refine ⟨17299327868068456533416645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46131540981515884089111053 17299327868068456533416645)
                ·
                  refine ⟨3243623975262835600015621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17299327868068456533416645 3243623975262835600015621)
                  ·
                    refine ⟨608179495361781675002929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3243623975262835600015621 608179495361781675002929)
                    ·
                      rfl

theorem cell23_3553276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 4, 4].length) (baseStart_3553276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3553276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3553276 prefixEnd_3553276 := by exact prefixLift 3553276
  have htrace : WordTrace (prefixWord ++ tailWord_3553276) baseStart_3553276 baseEnd_3553276 := by
    simpa [prefixWord, tailWord_3553276, baseEnd_3553276] using wordTrace_append hprefix tailTrace_3553276
  have hstable : (prefixWord ++ tailWord_3553276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553276).length < 2 ^ (prefixWord ++ tailWord_3553276).sum := by decide
  have hdescent : baseEnd_3553276 < baseStart_3553276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553313 : List Nat := [1, 2, 3, 2, 4, 1, 1, 2, 1, 2, 4]
def baseStart_3553313 : Nat := 118140960795 + 3553313 * 2 ^ 59
def prefixEnd_3553313 : Nat := 4983230072969 + 3 ^ 40 * 3553313 * 2
def baseEnd_3553313 : Nat := 1824557484869561380246117

theorem tailTrace_3553313 : CollatzResearch.WordTrace tailWord_3553313 prefixEnd_3553313 1824557484869561380246117 := by
  unfold tailWord_3553313
  simp only [CollatzResearch.WordTrace]
  refine ⟨129599972175961333391112593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86399981450640888927408395 129599972175961333391112593)
  ·
    refine ⟨97199979131971000043334445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129599972175961333391112593 97199979131971000043334445)
    ·
      refine ⟨36449992174489125016250417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97199979131971000043334445 36449992174489125016250417)
      ·
        refine ⟨27337494130866843762187813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36449992174489125016250417 27337494130866843762187813)
        ·
          refine ⟨5125780149537533205410215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27337494130866843762187813 5125780149537533205410215)
          ·
            refine ⟨7688670224306299808115323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5125780149537533205410215 7688670224306299808115323)
            ·
              refine ⟨11533005336459449712172985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7688670224306299808115323 11533005336459449712172985)
              ·
                refine ⟨8649754002344587284129739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11533005336459449712172985 8649754002344587284129739)
                ·
                  refine ⟨12974631003516880926194609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8649754002344587284129739 12974631003516880926194609)
                  ·
                    refine ⟨9730973252637660694645957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12974631003516880926194609 9730973252637660694645957)
                    ·
                      refine ⟨1824557484869561380246117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9730973252637660694645957 1824557484869561380246117)
                      ·
                        rfl

theorem cell23_3553313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_3553313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3553313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3553313 prefixEnd_3553313 := by exact prefixLift 3553313
  have htrace : WordTrace (prefixWord ++ tailWord_3553313) baseStart_3553313 baseEnd_3553313 := by
    simpa [prefixWord, tailWord_3553313, baseEnd_3553313] using wordTrace_append hprefix tailTrace_3553313
  have hstable : (prefixWord ++ tailWord_3553313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553313).length < 2 ^ (prefixWord ++ tailWord_3553313).sum := by decide
  have hdescent : baseEnd_3553313 < baseStart_3553313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553333 : List Nat := [1, 3, 3, 1, 1, 1, 2, 3, 4, 1, 3]
def baseStart_3553333 : Nat := 118140960795 + 3553333 * 2 ^ 59
def prefixEnd_3553333 : Nat := 4983230072969 + 3 ^ 40 * 3553333 * 2
def baseEnd_3553333 : Nat := 1824567754482651301996025

theorem tailTrace_3553333 : CollatzResearch.WordTrace tailWord_3553333 prefixEnd_3553333 1824567754482651301996025 := by
  unfold tailWord_3553333
  simp only [CollatzResearch.WordTrace]
  refine ⟨129600701635888876806840653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86400467757259251204560435 129600701635888876806840653)
  ·
    refine ⟨48600263113458328802565245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129600701635888876806840653 48600263113458328802565245)
    ·
      refine ⟨18225098667546873300961967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48600263113458328802565245 18225098667546873300961967)
      ·
        refine ⟨27337648001320309951442951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18225098667546873300961967 27337648001320309951442951)
        ·
          refine ⟨41006472001980464927164427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27337648001320309951442951 41006472001980464927164427)
          ·
            refine ⟨61509708002970697390746641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41006472001980464927164427 61509708002970697390746641)
            ·
              refine ⟨46132281002228023043059981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61509708002970697390746641 46132281002228023043059981)
              ·
                refine ⟨17299605375835508641147493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46132281002228023043059981 17299605375835508641147493)
                ·
                  refine ⟨3243676007969157870215155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17299605375835508641147493 3243676007969157870215155)
                  ·
                    refine ⟨4865514011953736805322733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3243676007969157870215155 4865514011953736805322733)
                    ·
                      refine ⟨1824567754482651301996025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4865514011953736805322733 1824567754482651301996025)
                      ·
                        rfl

theorem cell23_3553333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 4, 1, 3].length) (baseStart_3553333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3553333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3553333 prefixEnd_3553333 := by exact prefixLift 3553333
  have htrace : WordTrace (prefixWord ++ tailWord_3553333) baseStart_3553333 baseEnd_3553333 := by
    simpa [prefixWord, tailWord_3553333, baseEnd_3553333] using wordTrace_append hprefix tailTrace_3553333
  have hstable : (prefixWord ++ tailWord_3553333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553333).length < 2 ^ (prefixWord ++ tailWord_3553333).sum := by decide
  have hdescent : baseEnd_3553333 < baseStart_3553333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553334 : List Nat := [5, 1, 2, 1, 1, 1, 3, 4, 1, 2, 2]
def baseStart_3553334 : Nat := 118140960795 + 3553334 * 2 ^ 59
def prefixEnd_3553334 : Nat := 4983230072969 + 3 ^ 40 * 3553334 * 2
def baseEnd_3553334 : Nat := 1824568267963305798083521

theorem tailTrace_3553334 : CollatzResearch.WordTrace tailWord_3553334 prefixEnd_3553334 1824568267963305798083521 := by
  unfold tailWord_3553334
  simp only [CollatzResearch.WordTrace]
  refine ⟨8100046131805328373601691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86400492072590169318418037 8100046131805328373601691)
  ·
    refine ⟨12150069197707992560402537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8100046131805328373601691 12150069197707992560402537)
    ·
      refine ⟨9112551898280994420301903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12150069197707992560402537 9112551898280994420301903)
      ·
        refine ⟨13668827847421491630452855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9112551898280994420301903 13668827847421491630452855)
        ·
          refine ⟨20503241771132237445679283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13668827847421491630452855 20503241771132237445679283)
          ·
            refine ⟨30754862656698356168518925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20503241771132237445679283 30754862656698356168518925)
            ·
              refine ⟨11533073496261883563194597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30754862656698356168518925 11533073496261883563194597)
              ·
                refine ⟨2162451280549103168098987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11533073496261883563194597 2162451280549103168098987)
                ·
                  refine ⟨3243676920823654752148481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2162451280549103168098987 3243676920823654752148481)
                  ·
                    refine ⟨2432757690617741064111361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3243676920823654752148481 2432757690617741064111361)
                    ·
                      refine ⟨1824568267963305798083521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2432757690617741064111361 1824568267963305798083521)
                      ·
                        rfl

theorem cell23_3553334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_3553334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3553334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3553334 prefixEnd_3553334 := by exact prefixLift 3553334
  have htrace : WordTrace (prefixWord ++ tailWord_3553334) baseStart_3553334 baseEnd_3553334 := by
    simpa [prefixWord, tailWord_3553334, baseEnd_3553334] using wordTrace_append hprefix tailTrace_3553334
  have hstable : (prefixWord ++ tailWord_3553334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553334).length < 2 ^ (prefixWord ++ tailWord_3553334).sum := by decide
  have hdescent : baseEnd_3553334 < baseStart_3553334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553343 : List Nat := [1, 1, 2, 2, 3, 1, 3, 2, 3, 3, 2]
def baseStart_3553343 : Nat := 118140960795 + 3553343 * 2 ^ 59
def prefixEnd_3553343 : Nat := 4983230072969 + 3 ^ 40 * 3553343 * 2
def baseEnd_3553343 : Nat := 1824572889289196262870979

theorem tailTrace_3553343 : CollatzResearch.WordTrace tailWord_3553343 prefixEnd_3553343 1824572889289196262870979 := by
  unfold tailWord_3553343
  simp only [CollatzResearch.WordTrace]
  refine ⟨129601066365852648514704683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86400710910568432343136455 129601066365852648514704683)
  ·
    refine ⟨194401599548778972772057025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129601066365852648514704683 194401599548778972772057025)
    ·
      refine ⟨145801199661584229579042769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194401599548778972772057025 145801199661584229579042769)
      ·
        refine ⟨109350899746188172184282077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145801199661584229579042769 109350899746188172184282077)
        ·
          refine ⟨41006587404820564569105779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109350899746188172184282077 41006587404820564569105779)
          ·
            refine ⟨61509881107230846853658669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41006587404820564569105779 61509881107230846853658669)
            ·
              refine ⟨23066205415211567570122001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61509881107230846853658669 23066205415211567570122001)
              ·
                refine ⟨17299654061408675677591501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23066205415211567570122001 17299654061408675677591501)
                ·
                  refine ⟨6487370273028253379096813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17299654061408675677591501 6487370273028253379096813)
                  ·
                    refine ⟨2432763852385595017161305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6487370273028253379096813 2432763852385595017161305)
                    ·
                      refine ⟨1824572889289196262870979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2432763852385595017161305 1824572889289196262870979)
                      ·
                        rfl

theorem cell23_3553343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 3, 3, 2].length) (baseStart_3553343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3553343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3553343 prefixEnd_3553343 := by exact prefixLift 3553343
  have htrace : WordTrace (prefixWord ++ tailWord_3553343) baseStart_3553343 baseEnd_3553343 := by
    simpa [prefixWord, tailWord_3553343, baseEnd_3553343] using wordTrace_append hprefix tailTrace_3553343
  have hstable : (prefixWord ++ tailWord_3553343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553343).length < 2 ^ (prefixWord ++ tailWord_3553343).sum := by decide
  have hdescent : baseEnd_3553343 < baseStart_3553343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553447 : List Nat := [1, 1, 6, 2, 3, 1, 1, 1, 7]
def baseStart_3553447 : Nat := 118140960795 + 3553447 * 2 ^ 59
def prefixEnd_3553447 : Nat := 4983230072969 + 3 ^ 40 * 3553447 * 2
def baseEnd_3553447 : Nat := 202736254586362650663389

theorem tailTrace_3553447 : CollatzResearch.WordTrace tailWord_3553447 prefixEnd_3553447 202736254586362650663389 := by
  unfold tailWord_3553447
  simp only [CollatzResearch.WordTrace]
  refine ⟨129604859557475874276490595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86403239704983916184327063 129604859557475874276490595)
  ·
    refine ⟨194407289336213811414735893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129604859557475874276490595 194407289336213811414735893)
    ·
      refine ⟨9112841687635022410065745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 194407289336213811414735893 9112841687635022410065745)
      ·
        refine ⟨6834631265726266807549309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9112841687635022410065745 6834631265726266807549309)
        ·
          refine ⟨2562986724647350052830991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6834631265726266807549309 2562986724647350052830991)
          ·
            refine ⟨3844480086971025079246487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2562986724647350052830991 3844480086971025079246487)
            ·
              refine ⟨5766720130456537618869731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3844480086971025079246487 5766720130456537618869731)
              ·
                refine ⟨8650080195684806428304597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5766720130456537618869731 8650080195684806428304597)
                ·
                  refine ⟨202736254586362650663389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8650080195684806428304597 202736254586362650663389)
                  ·
                    rfl

theorem cell23_3553447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 1, 7].length) (baseStart_3553447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3553447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3553447 prefixEnd_3553447 := by exact prefixLift 3553447
  have htrace : WordTrace (prefixWord ++ tailWord_3553447) baseStart_3553447 baseEnd_3553447 := by
    simpa [prefixWord, tailWord_3553447, baseEnd_3553447] using wordTrace_append hprefix tailTrace_3553447
  have hstable : (prefixWord ++ tailWord_3553447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553447).length < 2 ^ (prefixWord ++ tailWord_3553447).sum := by decide
  have hdescent : baseEnd_3553447 < baseStart_3553447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553453 : List Nat := [1, 5, 2, 1, 2, 1, 1, 1, 1, 1, 7]
def baseStart_3553453 : Nat := 118140960795 + 3553453 * 2 ^ 59
def prefixEnd_3553453 : Nat := 4983230072969 + 3 ^ 40 * 3553453 * 2
def baseEnd_3553453 : Nat := 1824629372161190832495473

theorem tailTrace_3553453 : CollatzResearch.WordTrace tailWord_3553453 prefixEnd_3553453 1824629372161190832495473 := by
  unfold tailWord_3553453
  simp only [CollatzResearch.WordTrace]
  refine ⟨129605078395454137301209013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86403385596969424867472675 129605078395454137301209013)
  ·
    refine ⟨12150476099573825371988345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 129605078395454137301209013 12150476099573825371988345)
    ·
      refine ⟨9112857074680369028991259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12150476099573825371988345 9112857074680369028991259)
      ·
        refine ⟨13669285612020553543486889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9112857074680369028991259 13669285612020553543486889)
        ·
          refine ⟨10251964209015415157615167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13669285612020553543486889 10251964209015415157615167)
          ·
            refine ⟨15377946313523122736422751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10251964209015415157615167 15377946313523122736422751)
            ·
              refine ⟨23066919470284684104634127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15377946313523122736422751 23066919470284684104634127)
              ·
                refine ⟨34600379205427026156951191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23066919470284684104634127 34600379205427026156951191)
                ·
                  refine ⟨51900568808140539235426787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34600379205427026156951191 51900568808140539235426787)
                  ·
                    refine ⟨77850853212210808853140181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51900568808140539235426787 77850853212210808853140181)
                    ·
                      refine ⟨1824629372161190832495473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 77850853212210808853140181 1824629372161190832495473)
                      ·
                        rfl

theorem cell23_3553453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_3553453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3553453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3553453 prefixEnd_3553453 := by exact prefixLift 3553453
  have htrace : WordTrace (prefixWord ++ tailWord_3553453) baseStart_3553453 baseEnd_3553453 := by
    simpa [prefixWord, tailWord_3553453, baseEnd_3553453] using wordTrace_append hprefix tailTrace_3553453
  have hstable : (prefixWord ++ tailWord_3553453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553453).length < 2 ^ (prefixWord ++ tailWord_3553453).sum := by decide
  have hdescent : baseEnd_3553453 < baseStart_3553453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553530 : List Nat := [3, 1, 1, 1, 1, 5, 1, 1, 5, 1, 3]
def baseStart_3553530 : Nat := 118140960795 + 3553530 * 2 ^ 59
def prefixEnd_3553530 : Nat := 4983230072969 + 3 ^ 40 * 3553530 * 2
def baseEnd_3553530 : Nat := 1824668910171587031232619

theorem tailTrace_3553530 : CollatzResearch.WordTrace tailWord_3553530 prefixEnd_3553530 1824668910171587031232619 := by
  unfold tailWord_3553530
  simp only [CollatzResearch.WordTrace]
  refine ⟨32401971704043794862940511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86405257877450119634508029 32401971704043794862940511)
  ·
    refine ⟨48602957556065692294410767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32401971704043794862940511 48602957556065692294410767)
    ·
      refine ⟨72904436334098538441616151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48602957556065692294410767 72904436334098538441616151)
      ·
        refine ⟨109356654501147807662424227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72904436334098538441616151 109356654501147807662424227)
        ·
          refine ⟨164034981751721711493636341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109356654501147807662424227 164034981751721711493636341)
          ·
            refine ⟨15378279539223910452528407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 164034981751721711493636341 15378279539223910452528407)
            ·
              refine ⟨23067419308835865678792611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15378279539223910452528407 23067419308835865678792611)
              ·
                refine ⟨34601128963253798518188917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23067419308835865678792611 34601128963253798518188917)
                ·
                  refine ⟨3243855840305043611080211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34601128963253798518188917 3243855840305043611080211)
                  ·
                    refine ⟨4865783760457565416620317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3243855840305043611080211 4865783760457565416620317)
                    ·
                      refine ⟨1824668910171587031232619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4865783760457565416620317 1824668910171587031232619)
                      ·
                        rfl

theorem cell23_3553530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 5, 1, 3].length) (baseStart_3553530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3553530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3553530 prefixEnd_3553530 := by exact prefixLift 3553530
  have htrace : WordTrace (prefixWord ++ tailWord_3553530) baseStart_3553530 baseEnd_3553530 := by
    simpa [prefixWord, tailWord_3553530, baseEnd_3553530] using wordTrace_append hprefix tailTrace_3553530
  have hstable : (prefixWord ++ tailWord_3553530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553530).length < 2 ^ (prefixWord ++ tailWord_3553530).sum := by decide
  have hdescent : baseEnd_3553530 < baseStart_3553530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553550 : List Nat := [4, 1, 1, 2, 1, 2, 3, 3, 1, 5]
def baseStart_3553550 : Nat := 118140960795 + 3553550 * 2 ^ 59
def prefixEnd_3553550 : Nat := 4983230072969 + 3 ^ 40 * 3553550 * 2
def baseEnd_3553550 : Nat := 608226393261558984327509

theorem tailTrace_3553550 : CollatzResearch.WordTrace tailWord_3553550 prefixEnd_3553550 608226393261558984327509 := by
  unfold tailWord_3553550
  simp only [CollatzResearch.WordTrace]
  refine ⟨16201077034512840358436263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86405744184068481911660069 16201077034512840358436263)
  ·
    refine ⟨24301615551769260537654395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16201077034512840358436263 24301615551769260537654395)
    ·
      refine ⟨36452423327653890806481593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24301615551769260537654395 36452423327653890806481593)
      ·
        refine ⟨27339317495740418104861195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36452423327653890806481593 27339317495740418104861195)
        ·
          refine ⟨41008976243610627157291793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27339317495740418104861195 41008976243610627157291793)
          ·
            refine ⟨30756732182707970367968845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41008976243610627157291793 30756732182707970367968845)
            ·
              refine ⟨11533774568515488887988317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30756732182707970367968845 11533774568515488887988317)
              ·
                refine ⟨4325165463193308332995619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11533774568515488887988317 4325165463193308332995619)
                ·
                  refine ⟨6487748194789962499493429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4325165463193308332995619 6487748194789962499493429)
                  ·
                    refine ⟨608226393261558984327509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6487748194789962499493429 608226393261558984327509)
                    ·
                      rfl

theorem cell23_3553550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 3, 1, 5].length) (baseStart_3553550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3553550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3553550 prefixEnd_3553550 := by exact prefixLift 3553550
  have htrace : WordTrace (prefixWord ++ tailWord_3553550) baseStart_3553550 baseEnd_3553550 := by
    simpa [prefixWord, tailWord_3553550, baseEnd_3553550] using wordTrace_append hprefix tailTrace_3553550
  have hstable : (prefixWord ++ tailWord_3553550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553550).length < 2 ^ (prefixWord ++ tailWord_3553550).sum := by decide
  have hdescent : baseEnd_3553550 < baseStart_3553550 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3553580 : List Nat := [2, 2, 1, 1, 1, 3, 2, 5, 2, 4]
def baseStart_3553580 : Nat := 118140960795 + 3553580 * 2 ^ 59
def prefixEnd_3553580 : Nat := 4983230072969 + 3 ^ 40 * 3553580 * 2
def baseEnd_3553580 : Nat := 608231528068103945202463

theorem tailTrace_3553580 : CollatzResearch.WordTrace tailWord_3553580 prefixEnd_3553580 608231528068103945202463 := by
  unfold tailWord_3553580
  simp only [CollatzResearch.WordTrace]
  refine ⟨64804855232997018995541097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86406473643996025327388129 64804855232997018995541097)
  ·
    refine ⟨48603641424747764246655823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64804855232997018995541097 48603641424747764246655823)
    ·
      refine ⟨72905462137121646369983735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48603641424747764246655823 72905462137121646369983735)
      ·
        refine ⟨109358193205682469554975603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72905462137121646369983735 109358193205682469554975603)
        ·
          refine ⟨164037289808523704332463405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109358193205682469554975603 164037289808523704332463405)
          ·
            refine ⟨61513983678196389124673777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164037289808523704332463405 61513983678196389124673777)
            ·
              refine ⟨46135487758647291843505333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61513983678196389124673777 46135487758647291843505333)
              ·
                refine ⟨4325201977373183610328625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46135487758647291843505333 4325201977373183610328625)
                ·
                  refine ⟨3243901483029887707746469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4325201977373183610328625 3243901483029887707746469)
                  ·
                    refine ⟨608231528068103945202463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3243901483029887707746469 608231528068103945202463)
                    ·
                      rfl

theorem cell23_3553580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 4].length) (baseStart_3553580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3553580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3553580 prefixEnd_3553580 := by exact prefixLift 3553580
  have htrace : WordTrace (prefixWord ++ tailWord_3553580) baseStart_3553580 baseEnd_3553580 := by
    simpa [prefixWord, tailWord_3553580, baseEnd_3553580] using wordTrace_append hprefix tailTrace_3553580
  have hstable : (prefixWord ++ tailWord_3553580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3553580).length < 2 ^ (prefixWord ++ tailWord_3553580).sum := by decide
  have hdescent : baseEnd_3553580 < baseStart_3553580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3553580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
