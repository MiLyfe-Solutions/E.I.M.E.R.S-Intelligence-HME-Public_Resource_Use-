import V185TrunkScan23Chunk0609

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3606796 : List Nat := [2, 2, 1, 2, 2, 2, 3, 1, 3, 1, 4]
def baseStart_3606796 : Nat := 118140960795 + 3606796 * 2 ^ 59
def prefixEnd_3606796 : Nat := 4983230072969 + 3 ^ 40 * 3606796 * 2
def baseEnd_3606796 : Nat := 1852019970713975627762653

theorem tailTrace_3606796 : CollatzResearch.WordTrace tailWord_3606796 prefixEnd_3606796 1852019970713975627762653 := by
  unfold tailWord_3606796
  simp only [CollatzResearch.WordTrace]
  refine ⟨65775328720600779280152121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87700438294134372373536161 65775328720600779280152121)
  ·
    refine ⟨49331496540450584460114091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65775328720600779280152121 49331496540450584460114091)
    ·
      refine ⟨73997244810675876690171137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49331496540450584460114091 73997244810675876690171137)
      ·
        refine ⟨55497933608006907517628353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73997244810675876690171137 55497933608006907517628353)
        ·
          refine ⟨41623450206005180638221265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55497933608006907517628353 41623450206005180638221265)
          ·
            refine ⟨31217587654503885478665949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41623450206005180638221265 31217587654503885478665949)
            ·
              refine ⟨11706595370438957054499731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31217587654503885478665949 11706595370438957054499731)
              ·
                refine ⟨17559893055658435581749597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11706595370438957054499731 17559893055658435581749597)
                ·
                  refine ⟨6584959895871913343156099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17559893055658435581749597 6584959895871913343156099)
                  ·
                    refine ⟨9877439843807870014734149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6584959895871913343156099 9877439843807870014734149)
                    ·
                      refine ⟨1852019970713975627762653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9877439843807870014734149 1852019970713975627762653)
                      ·
                        rfl

theorem cell23_3606796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 3, 1, 4].length) (baseStart_3606796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3606796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3606796 prefixEnd_3606796 := by exact prefixLift 3606796
  have htrace : WordTrace (prefixWord ++ tailWord_3606796) baseStart_3606796 baseEnd_3606796 := by
    simpa [prefixWord, tailWord_3606796, baseEnd_3606796] using wordTrace_append hprefix tailTrace_3606796
  have hstable : (prefixWord ++ tailWord_3606796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606796).length < 2 ^ (prefixWord ++ tailWord_3606796).sum := by decide
  have hdescent : baseEnd_3606796 < baseStart_3606796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606799 : List Nat := [1, 1, 2, 1, 1, 1, 3, 4, 3, 1, 5]
def baseStart_3606799 : Nat := 118140960795 + 3606799 * 2 ^ 59
def prefixEnd_3606799 : Nat := 4983230072969 + 3 ^ 40 * 3606799 * 2
def baseEnd_3606799 : Nat := 1852021511155939116025139

theorem tailTrace_3606799 : CollatzResearch.WordTrace tailWord_3606799 prefixEnd_3606799 1852021511155939116025139 := by
  unfold tailWord_3606799
  simp only [CollatzResearch.WordTrace]
  refine ⟨131550766860190690072663451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87700511240127126715108967 131550766860190690072663451)
  ·
    refine ⟨197326150290286035108995177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131550766860190690072663451 197326150290286035108995177)
    ·
      refine ⟨147994612717714526331746383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197326150290286035108995177 147994612717714526331746383)
      ·
        refine ⟨221991919076571789497619575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147994612717714526331746383 221991919076571789497619575)
        ·
          refine ⟨332987878614857684246429363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221991919076571789497619575 332987878614857684246429363)
          ·
            refine ⟨499481817922286526369644045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332987878614857684246429363 499481817922286526369644045)
            ·
              refine ⟨187305681720857447388616517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 499481817922286526369644045 187305681720857447388616517)
              ·
                refine ⟨35119815322660771385365597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 187305681720857447388616517 35119815322660771385365597)
                ·
                  refine ⟨13169930745997789269512099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35119815322660771385365597 13169930745997789269512099)
                  ·
                    refine ⟨19754896118996683904268149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13169930745997789269512099 19754896118996683904268149)
                    ·
                      refine ⟨1852021511155939116025139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19754896118996683904268149 1852021511155939116025139)
                      ·
                        rfl

theorem cell23_3606799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3, 1, 5].length) (baseStart_3606799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3606799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3606799 prefixEnd_3606799 := by exact prefixLift 3606799
  have htrace : WordTrace (prefixWord ++ tailWord_3606799) baseStart_3606799 baseEnd_3606799 := by
    simpa [prefixWord, tailWord_3606799, baseEnd_3606799] using wordTrace_append hprefix tailTrace_3606799
  have hstable : (prefixWord ++ tailWord_3606799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606799).length < 2 ^ (prefixWord ++ tailWord_3606799).sum := by decide
  have hdescent : baseEnd_3606799 < baseStart_3606799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606810 : List Nat := [3, 1, 1, 3, 4, 1, 3, 1, 1, 5]
def baseStart_3606810 : Nat := 118140960795 + 3606810 * 2 ^ 59
def prefixEnd_3606810 : Nat := 4983230072969 + 3 ^ 40 * 3606810 * 2
def baseEnd_3606810 : Nat := 617342386481046190995863

theorem tailTrace_3606810 : CollatzResearch.WordTrace tailWord_3606810 prefixEnd_3606810 617342386481046190995863 := by
  unfold tailWord_3606810
  simp only [CollatzResearch.WordTrace]
  refine ⟨32887792015787709737828471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87700778708767225967542589 32887792015787709737828471)
  ·
    refine ⟨49331688023681564606742707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32887792015787709737828471 49331688023681564606742707)
    ·
      refine ⟨73997532035522346910114061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49331688023681564606742707 73997532035522346910114061)
      ·
        refine ⟨27749074513320880091292773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73997532035522346910114061 27749074513320880091292773)
        ·
          refine ⟨5202951471247665017117395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27749074513320880091292773 5202951471247665017117395)
          ·
            refine ⟨7804427206871497525676093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5202951471247665017117395 7804427206871497525676093)
            ·
              refine ⟨2926660202576811572128535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7804427206871497525676093 2926660202576811572128535)
              ·
                refine ⟨4389990303865217358192803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2926660202576811572128535 4389990303865217358192803)
                ·
                  refine ⟨6584985455797826037289205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4389990303865217358192803 6584985455797826037289205)
                  ·
                    refine ⟨617342386481046190995863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6584985455797826037289205 617342386481046190995863)
                    ·
                      rfl

theorem cell23_3606810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3, 1, 1, 5].length) (baseStart_3606810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3606810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3606810 prefixEnd_3606810 := by exact prefixLift 3606810
  have htrace : WordTrace (prefixWord ++ tailWord_3606810) baseStart_3606810 baseEnd_3606810 := by
    simpa [prefixWord, tailWord_3606810, baseEnd_3606810] using wordTrace_append hprefix tailTrace_3606810
  have hstable : (prefixWord ++ tailWord_3606810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606810).length < 2 ^ (prefixWord ++ tailWord_3606810).sum := by decide
  have hdescent : baseEnd_3606810 < baseStart_3606810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606839 : List Nat := [1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 6]
def baseStart_3606839 : Nat := 118140960795 + 3606839 * 2 ^ 59
def prefixEnd_3606839 : Nat := 4983230072969 + 3 ^ 40 * 3606839 * 2
def baseEnd_3606839 : Nat := 1852042050382118959524955

theorem tailTrace_3606839 : CollatzResearch.WordTrace tailWord_3606839 prefixEnd_3606839 1852042050382118959524955 := by
  unfold tailWord_3606839
  simp only [CollatzResearch.WordTrace]
  refine ⟨131552225780045776904119571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87701483853363851269413047 131552225780045776904119571)
  ·
    refine ⟨197328338670068665356179357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131552225780045776904119571 197328338670068665356179357)
    ·
      refine ⟨73998127001275749508567259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197328338670068665356179357 73998127001275749508567259)
      ·
        refine ⟨110997190501913624262850889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73998127001275749508567259 110997190501913624262850889)
        ·
          refine ⟨83247892876435218197138167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110997190501913624262850889 83247892876435218197138167)
          ·
            refine ⟨124871839314652827295707251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83247892876435218197138167 124871839314652827295707251)
            ·
              refine ⟨187307758971979240943560877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124871839314652827295707251 187307758971979240943560877)
              ·
                refine ⟨70240409614492215353835329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 187307758971979240943560877 70240409614492215353835329)
                ·
                  refine ⟨52680307210869161515376497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70240409614492215353835329 52680307210869161515376497)
                  ·
                    refine ⟨39510230408151871136532373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52680307210869161515376497 39510230408151871136532373)
                    ·
                      refine ⟨1852042050382118959524955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39510230408151871136532373 1852042050382118959524955)
                      ·
                        rfl

theorem cell23_3606839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 6].length) (baseStart_3606839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3606839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3606839 prefixEnd_3606839 := by exact prefixLift 3606839
  have htrace : WordTrace (prefixWord ++ tailWord_3606839) baseStart_3606839 baseEnd_3606839 := by
    simpa [prefixWord, tailWord_3606839, baseEnd_3606839] using wordTrace_append hprefix tailTrace_3606839
  have hstable : (prefixWord ++ tailWord_3606839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606839).length < 2 ^ (prefixWord ++ tailWord_3606839).sum := by decide
  have hdescent : baseEnd_3606839 < baseStart_3606839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606880 : List Nat := [2, 1, 1, 3, 5, 1, 1, 1, 4, 1, 3]
def baseStart_3606880 : Nat := 118140960795 + 3606880 * 2 ^ 59
def prefixEnd_3606880 : Nat := 4983230072969 + 3 ^ 40 * 3606880 * 2
def baseEnd_3606880 : Nat := 1852063103088953299112267

theorem tailTrace_3606880 : CollatzResearch.WordTrace tailWord_3606880 prefixEnd_3606880 1852063103088953299112267 := by
  unfold tailWord_3606880
  simp only [CollatzResearch.WordTrace]
  refine ⟨65776860586448620453181047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87702480781931493937574729 65776860586448620453181047)
  ·
    refine ⟨98665290879672930679771571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65776860586448620453181047 98665290879672930679771571)
    ·
      refine ⟨147997936319509396019657357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98665290879672930679771571 147997936319509396019657357)
      ·
        refine ⟨55499226119816023507371509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147997936319509396019657357 55499226119816023507371509)
        ·
          refine ⟨5203052448732752203816079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55499226119816023507371509 5203052448732752203816079)
          ·
            refine ⟨7804578673099128305724119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5203052448732752203816079 7804578673099128305724119)
            ·
              refine ⟨11706868009648692458586179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7804578673099128305724119 11706868009648692458586179)
              ·
                refine ⟨17560302014473038687879269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11706868009648692458586179 17560302014473038687879269)
                ·
                  refine ⟨3292556627713694753977363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17560302014473038687879269 3292556627713694753977363)
                  ·
                    refine ⟨4938834941570542130966045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3292556627713694753977363 4938834941570542130966045)
                    ·
                      refine ⟨1852063103088953299112267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4938834941570542130966045 1852063103088953299112267)
                      ·
                        rfl

theorem cell23_3606880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 4, 1, 3].length) (baseStart_3606880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3606880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3606880 prefixEnd_3606880 := by exact prefixLift 3606880
  have htrace : WordTrace (prefixWord ++ tailWord_3606880) baseStart_3606880 baseEnd_3606880 := by
    simpa [prefixWord, tailWord_3606880, baseEnd_3606880] using wordTrace_append hprefix tailTrace_3606880
  have hstable : (prefixWord ++ tailWord_3606880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606880).length < 2 ^ (prefixWord ++ tailWord_3606880).sum := by decide
  have hdescent : baseEnd_3606880 < baseStart_3606880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606896 : List Nat := [2, 1, 1, 1, 4, 3, 2, 1, 2, 6]
def baseStart_3606896 : Nat := 118140960795 + 3606896 * 2 ^ 59
def prefixEnd_3606896 : Nat := 4983230072969 + 3 ^ 40 * 3606896 * 2
def baseEnd_3606896 : Nat := 617357106259808412170731

theorem tailTrace_3606896 : CollatzResearch.WordTrace tailWord_3606896 prefixEnd_3606896 617357106259808412170731 := by
  unfold tailWord_3606896
  simp only [CollatzResearch.WordTrace]
  refine ⟨65777152370419637819472271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87702869827226183759296361 65777152370419637819472271)
  ·
    refine ⟨98665728555629456729208407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65777152370419637819472271 98665728555629456729208407)
    ·
      refine ⟨147998592833444185093812611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98665728555629456729208407 147998592833444185093812611)
      ·
        refine ⟨221997889250166277640718917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147998592833444185093812611 221997889250166277640718917)
        ·
          refine ⟨41624604234406177057634797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 221997889250166277640718917 41624604234406177057634797)
          ·
            refine ⟨15609226587902316396613049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41624604234406177057634797 15609226587902316396613049)
            ·
              refine ⟨11706919940926737297459787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15609226587902316396613049 11706919940926737297459787)
              ·
                refine ⟨17560379911390105946189681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11706919940926737297459787 17560379911390105946189681)
                ·
                  refine ⟨13170284933542579459642261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17560379911390105946189681 13170284933542579459642261)
                  ·
                    refine ⟨617357106259808412170731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13170284933542579459642261 617357106259808412170731)
                    ·
                      rfl

theorem cell23_3606896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 2, 6].length) (baseStart_3606896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3606896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3606896 prefixEnd_3606896 := by exact prefixLift 3606896
  have htrace : WordTrace (prefixWord ++ tailWord_3606896) baseStart_3606896 baseEnd_3606896 := by
    simpa [prefixWord, tailWord_3606896, baseEnd_3606896] using wordTrace_append hprefix tailTrace_3606896
  have hstable : (prefixWord ++ tailWord_3606896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606896).length < 2 ^ (prefixWord ++ tailWord_3606896).sum := by decide
  have hdescent : baseEnd_3606896 < baseStart_3606896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606903 : List Nat := [1, 1, 3, 1, 1, 2, 2, 5, 1, 4, 2]
def baseStart_3606903 : Nat := 118140960795 + 3606903 * 2 ^ 59
def prefixEnd_3606903 : Nat := 4983230072969 + 3 ^ 40 * 3606903 * 2
def baseEnd_3606903 : Nat := 1852074913144006709124661

theorem tailTrace_3606903 : CollatzResearch.WordTrace tailWord_3606903 prefixEnd_3606903 1852074913144006709124661 := by
  unfold tailWord_3606903
  simp only [CollatzResearch.WordTrace]
  refine ⟨131554560051813915834449363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87703040034542610556299575 131554560051813915834449363)
  ·
    refine ⟨197331840077720873751674045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131554560051813915834449363 197331840077720873751674045)
    ·
      refine ⟨73999440029145327656877767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197331840077720873751674045 73999440029145327656877767)
      ·
        refine ⟨110999160043717991485316651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73999440029145327656877767 110999160043717991485316651)
        ·
          refine ⟨166498740065576987227974977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110999160043717991485316651 166498740065576987227974977)
          ·
            refine ⟨124874055049182740420981233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166498740065576987227974977 124874055049182740420981233)
            ·
              refine ⟨93655541286887055315735925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124874055049182740420981233 93655541286887055315735925)
              ·
                refine ⟨8780206995645661435850243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93655541286887055315735925 8780206995645661435850243)
                ·
                  refine ⟨13170310493468492153775365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8780206995645661435850243 13170310493468492153775365)
                  ·
                    refine ⟨2469433217525342278832881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13170310493468492153775365 2469433217525342278832881)
                    ·
                      refine ⟨1852074913144006709124661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2469433217525342278832881 1852074913144006709124661)
                      ·
                        rfl

theorem cell23_3606903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5, 1, 4, 2].length) (baseStart_3606903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3606903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3606903 prefixEnd_3606903 := by exact prefixLift 3606903
  have htrace : WordTrace (prefixWord ++ tailWord_3606903) baseStart_3606903 baseEnd_3606903 := by
    simpa [prefixWord, tailWord_3606903, baseEnd_3606903] using wordTrace_append hprefix tailTrace_3606903
  have hstable : (prefixWord ++ tailWord_3606903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606903).length < 2 ^ (prefixWord ++ tailWord_3606903).sum := by decide
  have hdescent : baseEnd_3606903 < baseStart_3606903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606920 : List Nat := [2, 1, 3, 3, 1, 1, 1, 1, 6, 2, 2]
def baseStart_3606920 : Nat := 118140960795 + 3606920 * 2 ^ 59
def prefixEnd_3606920 : Nat := 4983230072969 + 3 ^ 40 * 3606920 * 2
def baseEnd_3606920 : Nat := 1852083642315133142612083

theorem tailTrace_3606920 : CollatzResearch.WordTrace tailWord_3606920 prefixEnd_3606920 1852083642315133142612083 := by
  unfold tailWord_3606920
  simp only [CollatzResearch.WordTrace]
  refine ⟨65777590046376163868909107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87703453395168218491878809 65777590046376163868909107)
  ·
    refine ⟨98666385069564245803363661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65777590046376163868909107 98666385069564245803363661)
    ·
      refine ⟨36999894401086592176261373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98666385069564245803363661 36999894401086592176261373)
      ·
        refine ⟨13874960400407472066098015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36999894401086592176261373 13874960400407472066098015)
        ·
          refine ⟨20812440600611208099147023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13874960400407472066098015 20812440600611208099147023)
          ·
            refine ⟨31218660900916812148720535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20812440600611208099147023 31218660900916812148720535)
            ·
              refine ⟨46827991351375218223080803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31218660900916812148720535 46827991351375218223080803)
              ·
                refine ⟨70241987027062827334621205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46827991351375218223080803 70241987027062827334621205)
                ·
                  refine ⟨3292593141893570031310369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 70241987027062827334621205 3292593141893570031310369)
                  ·
                    refine ⟨2469444856420177523482777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3292593141893570031310369 2469444856420177523482777)
                    ·
                      refine ⟨1852083642315133142612083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2469444856420177523482777 1852083642315133142612083)
                      ·
                        rfl

theorem cell23_3606920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_3606920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3606920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3606920 prefixEnd_3606920 := by exact prefixLift 3606920
  have htrace : WordTrace (prefixWord ++ tailWord_3606920) baseStart_3606920 baseEnd_3606920 := by
    simpa [prefixWord, tailWord_3606920, baseEnd_3606920] using wordTrace_append hprefix tailTrace_3606920
  have hstable : (prefixWord ++ tailWord_3606920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606920).length < 2 ^ (prefixWord ++ tailWord_3606920).sum := by decide
  have hdescent : baseEnd_3606920 < baseStart_3606920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606956 : List Nat := [2, 2, 1, 1, 1, 1, 3, 1, 6, 5]
def baseStart_3606956 : Nat := 118140960795 + 3606956 * 2 ^ 59
def prefixEnd_3606956 : Nat := 4983230072969 + 3 ^ 40 * 3606956 * 2
def baseEnd_3606956 : Nat := 617367375872898333920639

theorem tailTrace_3606956 : CollatzResearch.WordTrace tailWord_3606956 prefixEnd_3606956 617367375872898333920639 := by
  unfold tailWord_3606956
  simp only [CollatzResearch.WordTrace]
  refine ⟨65778246560310952943064361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87704328747081270590752481 65778246560310952943064361)
  ·
    refine ⟨49333684920233214707298271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65778246560310952943064361 49333684920233214707298271)
    ·
      refine ⟨74000527380349822060947407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49333684920233214707298271 74000527380349822060947407)
      ·
        refine ⟨111000791070524733091421111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74000527380349822060947407 111000791070524733091421111)
        ·
          refine ⟨166501186605787099637131667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111000791070524733091421111 166501186605787099637131667)
          ·
            refine ⟨249751779908680649455697501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166501186605787099637131667 249751779908680649455697501)
            ·
              refine ⟨93656917465755243545886563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 249751779908680649455697501 93656917465755243545886563)
              ·
                refine ⟨140485376198632865318829845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93656917465755243545886563 140485376198632865318829845)
                ·
                  refine ⟨6585252009310915561820149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 140485376198632865318829845 6585252009310915561820149)
                  ·
                    refine ⟨617367375872898333920639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6585252009310915561820149 617367375872898333920639)
                    ·
                      rfl

theorem cell23_3606956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 5].length) (baseStart_3606956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3606956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3606956 prefixEnd_3606956 := by exact prefixLift 3606956
  have htrace : WordTrace (prefixWord ++ tailWord_3606956) baseStart_3606956 baseEnd_3606956 := by
    simpa [prefixWord, tailWord_3606956, baseEnd_3606956] using wordTrace_append hprefix tailTrace_3606956
  have hstable : (prefixWord ++ tailWord_3606956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606956).length < 2 ^ (prefixWord ++ tailWord_3606956).sum := by decide
  have hdescent : baseEnd_3606956 < baseStart_3606956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606973 : List Nat := [1, 4, 1, 2, 2, 2, 1, 3, 2, 5]
def baseStart_3606973 : Nat := 118140960795 + 3606973 * 2 ^ 59
def prefixEnd_3606973 : Nat := 4983230072969 + 3 ^ 40 * 3606973 * 2
def baseEnd_3606973 : Nat := 617370285596607145083113

theorem tailTrace_3606973 : CollatzResearch.WordTrace tailWord_3606973 prefixEnd_3606973 617370285596607145083113 := by
  unfold tailWord_3606973
  simp only [CollatzResearch.WordTrace]
  refine ⟨131557113161560317789497573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87704742107706878526331715 131557113161560317789497573)
  ·
    refine ⟨24666958717792559585530795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131557113161560317789497573 24666958717792559585530795)
    ·
      refine ⟨37000438076688839378296193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24666958717792559585530795 37000438076688839378296193)
      ·
        refine ⟨27750328557516629533722145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37000438076688839378296193 27750328557516629533722145)
        ·
          refine ⟨20812746418137472150291609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27750328557516629533722145 20812746418137472150291609)
          ·
            refine ⟨15609559813603104112718707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20812746418137472150291609 15609559813603104112718707)
            ·
              refine ⟨23414339720404656169078061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15609559813603104112718707 23414339720404656169078061)
              ·
                refine ⟨8780377395151746063404273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23414339720404656169078061 8780377395151746063404273)
                ·
                  refine ⟨6585283046363809547553205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8780377395151746063404273 6585283046363809547553205)
                  ·
                    refine ⟨617370285596607145083113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6585283046363809547553205 617370285596607145083113)
                    ·
                      rfl

theorem cell23_3606973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 3, 2, 5].length) (baseStart_3606973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3606973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3606973 prefixEnd_3606973 := by exact prefixLift 3606973
  have htrace : WordTrace (prefixWord ++ tailWord_3606973) baseStart_3606973 baseEnd_3606973 := by
    simpa [prefixWord, tailWord_3606973, baseEnd_3606973] using wordTrace_append hprefix tailTrace_3606973
  have hstable : (prefixWord ++ tailWord_3606973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606973).length < 2 ^ (prefixWord ++ tailWord_3606973).sum := by decide
  have hdescent : baseEnd_3606973 < baseStart_3606973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3606993 : List Nat := [1, 2, 2, 1, 2, 1, 1, 2, 3, 6, 2]
def baseStart_3606993 : Nat := 118140960795 + 3606993 * 2 ^ 59
def prefixEnd_3606993 : Nat := 4983230072969 + 3 ^ 40 * 3606993 * 2
def baseEnd_3606993 : Nat := 1852121126402911356999247

theorem tailTrace_3606993 : CollatzResearch.WordTrace tailWord_3606993 prefixEnd_3606993 1852121126402911356999247 := by
  unfold tailWord_3606993
  simp only [CollatzResearch.WordTrace]
  refine ⟨131557842621487861205225633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87705228414325240803483755 131557842621487861205225633)
  ·
    refine ⟨98668381966115895903919225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131557842621487861205225633 98668381966115895903919225)
    ·
      refine ⟨74001286474586921927939419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98668381966115895903919225 74001286474586921927939419)
      ·
        refine ⟨111001929711880382891909129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74001286474586921927939419 111001929711880382891909129)
        ·
          refine ⟨83251447283910287168931847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111001929711880382891909129 83251447283910287168931847)
          ·
            refine ⟨124877170925865430753397771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83251447283910287168931847 124877170925865430753397771)
            ·
              refine ⟨187315756388798146130096657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124877170925865430753397771 187315756388798146130096657)
              ·
                refine ⟨140486817291598609597572493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187315756388798146130096657 140486817291598609597572493)
                ·
                  refine ⟨52682556484349478599089685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 140486817291598609597572493 52682556484349478599089685)
                  ·
                    refine ⟨2469494835203881809332329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 52682556484349478599089685 2469494835203881809332329)
                    ·
                      refine ⟨1852121126402911356999247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2469494835203881809332329 1852121126402911356999247)
                      ·
                        rfl

theorem cell23_3606993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 6, 2].length) (baseStart_3606993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3606993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3606993 prefixEnd_3606993 := by exact prefixLift 3606993
  have htrace : WordTrace (prefixWord ++ tailWord_3606993) baseStart_3606993 baseEnd_3606993 := by
    simpa [prefixWord, tailWord_3606993, baseEnd_3606993] using wordTrace_append hprefix tailTrace_3606993
  have hstable : (prefixWord ++ tailWord_3606993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3606993).length < 2 ^ (prefixWord ++ tailWord_3606993).sum := by decide
  have hdescent : baseEnd_3606993 < baseStart_3606993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3606993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607030 : List Nat := [5, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3]
def baseStart_3607030 : Nat := 118140960795 + 3607030 * 2 ^ 59
def prefixEnd_3607030 : Nat := 4983230072969 + 3 ^ 40 * 3607030 * 2
def baseEnd_3607030 : Nat := 1852140125187127712236577

theorem tailTrace_3607030 : CollatzResearch.WordTrace tailWord_3607030 prefixEnd_3607030 1852140125187127712236577 := by
  unfold tailWord_3607030
  simp only [CollatzResearch.WordTrace]
  refine ⟨8222449507647113532770159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87706128081569211016215029 8222449507647113532770159)
  ·
    refine ⟨12333674261470670299155239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8222449507647113532770159 12333674261470670299155239)
    ·
      refine ⟨18500511392206005448732859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12333674261470670299155239 18500511392206005448732859)
      ·
        refine ⟨27750767088309008173099289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18500511392206005448732859 27750767088309008173099289)
        ·
          refine ⟨20813075316231756129824467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27750767088309008173099289 20813075316231756129824467)
          ·
            refine ⟨31219612974347634194736701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20813075316231756129824467 31219612974347634194736701)
            ·
              refine ⟨11707354865380362823026263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31219612974347634194736701 11707354865380362823026263)
              ·
                refine ⟨17561032298070544234539395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11707354865380362823026263 17561032298070544234539395)
                ·
                  refine ⟨26341548447105816351809093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17561032298070544234539395 26341548447105816351809093)
                  ·
                    refine ⟨4939040333832340565964205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26341548447105816351809093 4939040333832340565964205)
                    ·
                      refine ⟨1852140125187127712236577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4939040333832340565964205 1852140125187127712236577)
                      ·
                        rfl

theorem cell23_3607030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_3607030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3607030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3607030 prefixEnd_3607030 := by exact prefixLift 3607030
  have htrace : WordTrace (prefixWord ++ tailWord_3607030) baseStart_3607030 baseEnd_3607030 := by
    simpa [prefixWord, tailWord_3607030, baseEnd_3607030] using wordTrace_append hprefix tailTrace_3607030
  have hstable : (prefixWord ++ tailWord_3607030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607030).length < 2 ^ (prefixWord ++ tailWord_3607030).sum := by decide
  have hdescent : baseEnd_3607030 < baseStart_3607030 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607037 : List Nat := [1, 4, 1, 1, 1, 3, 4, 3, 1, 4]
def baseStart_3607037 : Nat := 118140960795 + 3607037 * 2 ^ 59
def prefixEnd_3607037 : Nat := 4983230072969 + 3 ^ 40 * 3607037 * 2
def baseEnd_3607037 : Nat := 617381239850569728283015

theorem tailTrace_3607037 : CollatzResearch.WordTrace tailWord_3607037 prefixEnd_3607037 617381239850569728283015 := by
  unfold tailWord_3607037
  simp only [CollatzResearch.WordTrace]
  refine ⟨131559447433328456719827365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87706298288885637813218243 131559447433328456719827365)
  ·
    refine ⟨24667396393749085634967631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131559447433328456719827365 24667396393749085634967631)
    ·
      refine ⟨37001094590623628452451447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24667396393749085634967631 37001094590623628452451447)
      ·
        refine ⟨55501641885935442678677171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37001094590623628452451447 55501641885935442678677171)
        ·
          refine ⟨83252462828903164018015757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55501641885935442678677171 83252462828903164018015757)
          ·
            refine ⟨31219673560838686506755909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83252462828903164018015757 31219673560838686506755909)
            ·
              refine ⟨5853688792657253720016733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31219673560838686506755909 5853688792657253720016733)
              ·
                refine ⟨2195133297246470145006275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5853688792657253720016733 2195133297246470145006275)
                ·
                  refine ⟨3292699945869705217509413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2195133297246470145006275 3292699945869705217509413)
                  ·
                    refine ⟨617381239850569728283015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3292699945869705217509413 617381239850569728283015)
                    ·
                      rfl

theorem cell23_3607037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 3, 1, 4].length) (baseStart_3607037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3607037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3607037 prefixEnd_3607037 := by exact prefixLift 3607037
  have htrace : WordTrace (prefixWord ++ tailWord_3607037) baseStart_3607037 baseEnd_3607037 := by
    simpa [prefixWord, tailWord_3607037, baseEnd_3607037] using wordTrace_append hprefix tailTrace_3607037
  have hstable : (prefixWord ++ tailWord_3607037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607037).length < 2 ^ (prefixWord ++ tailWord_3607037).sum := by decide
  have hdescent : baseEnd_3607037 < baseStart_3607037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607056 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 7]
def baseStart_3607056 : Nat := 118140960795 + 3607056 * 2 ^ 59
def prefixEnd_3607056 : Nat := 4983230072969 + 3 ^ 40 * 3607056 * 2
def baseEnd_3607056 : Nat := 1852153475684144610511457

theorem tailTrace_3607056 : CollatzResearch.WordTrace tailWord_3607056 prefixEnd_3607056 1852153475684144610511457 := by
  unfold tailWord_3607056
  simp only [CollatzResearch.WordTrace]
  refine ⟨65780070210129811482384511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87706760280173081976512681 65780070210129811482384511)
  ·
    refine ⟨98670105315194717223576767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65780070210129811482384511 98670105315194717223576767)
    ·
      refine ⟨148005157972792075835365151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98670105315194717223576767 148005157972792075835365151)
      ·
        refine ⟨222007736959188113753047727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148005157972792075835365151 222007736959188113753047727)
        ·
          refine ⟨333011605438782170629571591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222007736959188113753047727 333011605438782170629571591)
          ·
            refine ⟨499517408158173255944357387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333011605438782170629571591 499517408158173255944357387)
            ·
              refine ⟨749276112237259883916536081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 499517408158173255944357387 749276112237259883916536081)
              ·
                refine ⟨561957084177944912937402061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 749276112237259883916536081 561957084177944912937402061)
                ·
                  refine ⟨210733906566729342351525773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 561957084177944912937402061 210733906566729342351525773)
                  ·
                    refine ⟨79025214962523503381822165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 210733906566729342351525773 79025214962523503381822165)
                    ·
                      refine ⟨1852153475684144610511457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 79025214962523503381822165 1852153475684144610511457)
                      ·
                        rfl

theorem cell23_3607056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 7].length) (baseStart_3607056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3607056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3607056 prefixEnd_3607056 := by exact prefixLift 3607056
  have htrace : WordTrace (prefixWord ++ tailWord_3607056) baseStart_3607056 baseEnd_3607056 := by
    simpa [prefixWord, tailWord_3607056, baseEnd_3607056] using wordTrace_append hprefix tailTrace_3607056
  have hstable : (prefixWord ++ tailWord_3607056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607056).length < 2 ^ (prefixWord ++ tailWord_3607056).sum := by decide
  have hdescent : baseEnd_3607056 < baseStart_3607056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607083 : List Nat := [1, 1, 1, 1, 2, 1, 3, 5, 3, 1, 4]
def baseStart_3607083 : Nat := 118140960795 + 3607083 * 2 ^ 59
def prefixEnd_3607083 : Nat := 4983230072969 + 3 ^ 40 * 3607083 * 2
def baseEnd_3607083 : Nat := 1852167339661816004873833

theorem tailTrace_3607083 : CollatzResearch.WordTrace tailWord_3607083 prefixEnd_3607083 1852167339661816004873833 := by
  unfold tailWord_3607083
  simp only [CollatzResearch.WordTrace]
  refine ⟨131561125191161806576001903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87707416794107871050667935 131561125191161806576001903)
  ·
    refine ⟨197341687786742709864002855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131561125191161806576001903 197341687786742709864002855)
    ·
      refine ⟨296012531680114064796004283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197341687786742709864002855 296012531680114064796004283)
      ·
        refine ⟨444018797520171097194006425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296012531680114064796004283 444018797520171097194006425)
        ·
          refine ⟨333014098140128322895504819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 444018797520171097194006425 333014098140128322895504819)
          ·
            refine ⟨499521147210192484343257229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333014098140128322895504819 499521147210192484343257229)
            ·
              refine ⟨187320430203822181628721461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 499521147210192484343257229 187320430203822181628721461)
              ·
                refine ⟨17561290331608329527692637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 187320430203822181628721461 17561290331608329527692637)
                ·
                  refine ⟨6585483874353123572884739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17561290331608329527692637 6585483874353123572884739)
                  ·
                    refine ⟨9878225811529685359327109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6585483874353123572884739 9878225811529685359327109)
                    ·
                      refine ⟨1852167339661816004873833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9878225811529685359327109 1852167339661816004873833)
                      ·
                        rfl

theorem cell23_3607083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 3, 1, 4].length) (baseStart_3607083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3607083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3607083 prefixEnd_3607083 := by exact prefixLift 3607083
  have htrace : WordTrace (prefixWord ++ tailWord_3607083) baseStart_3607083 baseEnd_3607083 := by
    simpa [prefixWord, tailWord_3607083, baseEnd_3607083] using wordTrace_append hprefix tailTrace_3607083
  have hstable : (prefixWord ++ tailWord_3607083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607083).length < 2 ^ (prefixWord ++ tailWord_3607083).sum := by decide
  have hdescent : baseEnd_3607083 < baseStart_3607083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607093 : List Nat := [1, 3, 3, 1, 1, 2, 2, 1, 3, 6]
def baseStart_3607093 : Nat := 118140960795 + 3607093 * 2 ^ 59
def prefixEnd_3607093 : Nat := 4983230072969 + 3 ^ 40 * 3607093 * 2
def baseEnd_3607093 : Nat := 617390824822786988582929

theorem tailTrace_3607093 : CollatzResearch.WordTrace tailWord_3607093 prefixEnd_3607093 617390824822786988582929 := by
  unfold tailWord_3607093
  simp only [CollatzResearch.WordTrace]
  refine ⟨131561489921125578283865933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87707659947417052189243955 131561489921125578283865933)
  ·
    refine ⟨49335558720422091856449725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131561489921125578283865933 49335558720422091856449725)
    ·
      refine ⟨18500834520158284446168647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49335558720422091856449725 18500834520158284446168647)
      ·
        refine ⟨27751251780237426669252971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18500834520158284446168647 27751251780237426669252971)
        ·
          refine ⟨41626877670356140003879457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27751251780237426669252971 41626877670356140003879457)
          ·
            refine ⟨31220158252767105002909593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41626877670356140003879457 31220158252767105002909593)
            ·
              refine ⟨23415118689575328752182195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31220158252767105002909593 23415118689575328752182195)
              ·
                refine ⟨35122678034362993128273293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23415118689575328752182195 35122678034362993128273293)
                ·
                  refine ⟨13171004262886122423102485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35122678034362993128273293 13171004262886122423102485)
                  ·
                    refine ⟨617390824822786988582929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13171004262886122423102485 617390824822786988582929)
                    ·
                      rfl

theorem cell23_3607093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_3607093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3607093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3607093 prefixEnd_3607093 := by exact prefixLift 3607093
  have htrace : WordTrace (prefixWord ++ tailWord_3607093) baseStart_3607093 baseEnd_3607093 := by
    simpa [prefixWord, tailWord_3607093, baseEnd_3607093] using wordTrace_append hprefix tailTrace_3607093
  have hstable : (prefixWord ++ tailWord_3607093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607093).length < 2 ^ (prefixWord ++ tailWord_3607093).sum := by decide
  have hdescent : baseEnd_3607093 < baseStart_3607093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607111 : List Nat := [1, 1, 4, 1, 4, 2, 3, 2, 1, 1, 3]
def baseStart_3607111 : Nat := 118140960795 + 3607111 * 2 ^ 59
def prefixEnd_3607111 : Nat := 4983230072969 + 3 ^ 40 * 3607111 * 2
def baseEnd_3607111 : Nat := 1852181717120141895323705

theorem tailTrace_3607111 : CollatzResearch.WordTrace tailWord_3607111 prefixEnd_3607111 1852181717120141895323705 := by
  unfold tailWord_3607111
  simp only [CollatzResearch.WordTrace]
  refine ⟨131562146435060367358021187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87708097623373578238680791 131562146435060367358021187)
  ·
    refine ⟨197343219652590551037031781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131562146435060367358021187 197343219652590551037031781)
    ·
      refine ⟨37001853684860728319443459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 197343219652590551037031781 37001853684860728319443459)
      ·
        refine ⟨55502780527291092479165189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37001853684860728319443459 55502780527291092479165189)
        ·
          refine ⟨10406771348867079839843473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55502780527291092479165189 10406771348867079839843473)
          ·
            refine ⟨7805078511650309879882605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10406771348867079839843473 7805078511650309879882605)
            ·
              refine ⟨2926904441868866204955977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7805078511650309879882605 2926904441868866204955977)
              ·
                refine ⟨2195178331401649653716983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2926904441868866204955977 2195178331401649653716983)
                ·
                  refine ⟨3292767497102474480575475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2195178331401649653716983 3292767497102474480575475)
                  ·
                    refine ⟨4939151245653711720863213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3292767497102474480575475 4939151245653711720863213)
                    ·
                      refine ⟨1852181717120141895323705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4939151245653711720863213 1852181717120141895323705)
                      ·
                        rfl

theorem cell23_3607111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3, 2, 1, 1, 3].length) (baseStart_3607111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3607111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3607111 prefixEnd_3607111 := by exact prefixLift 3607111
  have htrace : WordTrace (prefixWord ++ tailWord_3607111) baseStart_3607111 baseEnd_3607111 := by
    simpa [prefixWord, tailWord_3607111, baseEnd_3607111] using wordTrace_append hprefix tailTrace_3607111
  have hstable : (prefixWord ++ tailWord_3607111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607111).length < 2 ^ (prefixWord ++ tailWord_3607111).sum := by decide
  have hdescent : baseEnd_3607111 < baseStart_3607111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607137 : List Nat := [1, 2, 3, 1, 1, 4, 3, 2, 1, 2, 3]
def baseStart_3607137 : Nat := 118140960795 + 3607137 * 2 ^ 59
def prefixEnd_3607137 : Nat := 4983230072969 + 3 ^ 40 * 3607137 * 2
def baseEnd_3607137 : Nat := 1852195067617158793598585

theorem tailTrace_3607137 : CollatzResearch.WordTrace tailWord_3607137 prefixEnd_3607137 1852195067617158793598585 := by
  unfold tailWord_3607137
  simp only [CollatzResearch.WordTrace]
  refine ⟨131563094732966173798467665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87708729821977449198978443 131563094732966173798467665)
  ·
    refine ⟨98672321049724630348850749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131563094732966173798467665 98672321049724630348850749)
    ·
      refine ⟨37002120393646736380819031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98672321049724630348850749 37002120393646736380819031)
      ·
        refine ⟨55503180590470104571228547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37002120393646736380819031 55503180590470104571228547)
        ·
          refine ⟨83254770885705156856842821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55503180590470104571228547 83254770885705156856842821)
          ·
            refine ⟨15610269541069716910658029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83254770885705156856842821 15610269541069716910658029)
            ·
              refine ⟨5853851077901143841496761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15610269541069716910658029 5853851077901143841496761)
              ·
                refine ⟨4390388308425857881122571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5853851077901143841496761 4390388308425857881122571)
                ·
                  refine ⟨6585582462638786821683857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4390388308425857881122571 6585582462638786821683857)
                  ·
                    refine ⟨4939186846979090116262893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6585582462638786821683857 4939186846979090116262893)
                    ·
                      refine ⟨1852195067617158793598585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4939186846979090116262893 1852195067617158793598585)
                      ·
                        rfl

theorem cell23_3607137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 2, 1, 2, 3].length) (baseStart_3607137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3607137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3607137 prefixEnd_3607137 := by exact prefixLift 3607137
  have htrace : WordTrace (prefixWord ++ tailWord_3607137) baseStart_3607137 baseEnd_3607137 := by
    simpa [prefixWord, tailWord_3607137, baseEnd_3607137] using wordTrace_append hprefix tailTrace_3607137
  have hstable : (prefixWord ++ tailWord_3607137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607137).length < 2 ^ (prefixWord ++ tailWord_3607137).sum := by decide
  have hdescent : baseEnd_3607137 < baseStart_3607137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607154 : List Nat := [3, 2, 1, 2, 5, 1, 1, 1, 1, 1, 5]
def baseStart_3607154 : Nat := 118140960795 + 3607154 * 2 ^ 59
def prefixEnd_3607154 : Nat := 4983230072969 + 3 ^ 40 * 3607154 * 2
def baseEnd_3607154 : Nat := 1852203796788285227086007

theorem tailTrace_3607154 : CollatzResearch.WordTrace tailWord_3607154 prefixEnd_3607154 1852203796788285227086007 := by
  unfold tailWord_3607154
  simp only [CollatzResearch.WordTrace]
  refine ⟨32890928693476146425459129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87709143182603057134557677 32890928693476146425459129)
  ·
    refine ⟨24668196520107109819094347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32890928693476146425459129 24668196520107109819094347)
    ·
      refine ⟨37002294780160664728641521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24668196520107109819094347 37002294780160664728641521)
      ·
        refine ⟨27751721085120498546481141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37002294780160664728641521 27751721085120498546481141)
        ·
          refine ⟨2601723851730046738732607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27751721085120498546481141 2601723851730046738732607)
          ·
            refine ⟨3902585777595070108098911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2601723851730046738732607 3902585777595070108098911)
            ·
              refine ⟨5853878666392605162148367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3902585777595070108098911 5853878666392605162148367)
              ·
                refine ⟨8780817999588907743222551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5853878666392605162148367 8780817999588907743222551)
                ·
                  refine ⟨13171226999383361614833827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8780817999588907743222551 13171226999383361614833827)
                  ·
                    refine ⟨19756840499075042422250741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13171226999383361614833827 19756840499075042422250741)
                    ·
                      refine ⟨1852203796788285227086007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19756840499075042422250741 1852203796788285227086007)
                      ·
                        rfl

theorem cell23_3607154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 1, 1, 1, 5].length) (baseStart_3607154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3607154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3607154 prefixEnd_3607154 := by exact prefixLift 3607154
  have htrace : WordTrace (prefixWord ++ tailWord_3607154) baseStart_3607154 baseEnd_3607154 := by
    simpa [prefixWord, tailWord_3607154, baseEnd_3607154] using wordTrace_append hprefix tailTrace_3607154
  have hstable : (prefixWord ++ tailWord_3607154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607154).length < 2 ^ (prefixWord ++ tailWord_3607154).sum := by decide
  have hdescent : baseEnd_3607154 < baseStart_3607154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607168 : List Nat := [2, 1, 1, 2, 1, 7, 2, 2, 1, 2, 2]
def baseStart_3607168 : Nat := 118140960795 + 3607168 * 2 ^ 59
def prefixEnd_3607168 : Nat := 4983230072969 + 3 ^ 40 * 3607168 * 2
def baseEnd_3607168 : Nat := 1852210985517448172310943

theorem tailTrace_3607168 : CollatzResearch.WordTrace tailWord_3607168 prefixEnd_3607168 1852210985517448172310943 := by
  unfold tailWord_3607168
  simp only [CollatzResearch.WordTrace]
  refine ⟨65782112697926933046423079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87709483597235910728564105 65782112697926933046423079)
  ·
    refine ⟨98673169046890399569634619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65782112697926933046423079 98673169046890399569634619)
    ·
      refine ⟨148009753570335599354451929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98673169046890399569634619 148009753570335599354451929)
      ·
        refine ⟨111007315177751699515838947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148009753570335599354451929 111007315177751699515838947)
        ·
          refine ⟨166510972766627549273758421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111007315177751699515838947 166510972766627549273758421)
          ·
            refine ⟨3902600924217833186103713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 166510972766627549273758421 3902600924217833186103713)
            ·
              refine ⟨2926950693163374889577785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3902600924217833186103713 2926950693163374889577785)
              ·
                refine ⟨2195213019872531167183339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2926950693163374889577785 2195213019872531167183339)
                ·
                  refine ⟨3292819529808796750775009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2195213019872531167183339 3292819529808796750775009)
                  ·
                    refine ⟨2469614647356597563081257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3292819529808796750775009 2469614647356597563081257)
                    ·
                      refine ⟨1852210985517448172310943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2469614647356597563081257 1852210985517448172310943)
                      ·
                        rfl

theorem cell23_3607168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2, 2, 1, 2, 2].length) (baseStart_3607168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3607168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3607168 prefixEnd_3607168 := by exact prefixLift 3607168
  have htrace : WordTrace (prefixWord ++ tailWord_3607168) baseStart_3607168 baseEnd_3607168 := by
    simpa [prefixWord, tailWord_3607168, baseEnd_3607168] using wordTrace_append hprefix tailTrace_3607168
  have hstable : (prefixWord ++ tailWord_3607168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607168).length < 2 ^ (prefixWord ++ tailWord_3607168).sum := by decide
  have hdescent : baseEnd_3607168 < baseStart_3607168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607183 : List Nat := [1, 1, 2, 1, 1, 1, 1, 7, 2, 6]
def baseStart_3607183 : Nat := 118140960795 + 3607183 * 2 ^ 59
def prefixEnd_3607183 : Nat := 4983230072969 + 3 ^ 40 * 3607183 * 2
def baseEnd_3607183 : Nat := 617406229242421871207791

theorem tailTrace_3607183 : CollatzResearch.WordTrace tailWord_3607183 prefixEnd_3607183 617406229242421871207791 := by
  unfold tailWord_3607183
  simp only [CollatzResearch.WordTrace]
  refine ⟨131564772490799523654642203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87709848327199682436428135 131564772490799523654642203)
  ·
    refine ⟨197347158736199285481963305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131564772490799523654642203 197347158736199285481963305)
    ·
      refine ⟨148010369052149464111472479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197347158736199285481963305 148010369052149464111472479)
      ·
        refine ⟨222015553578224196167208719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148010369052149464111472479 222015553578224196167208719)
        ·
          refine ⟨333023330367336294250813079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222015553578224196167208719 333023330367336294250813079)
          ·
            refine ⟨499534995551004441376219619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333023330367336294250813079 499534995551004441376219619)
            ·
              refine ⟨749302493326506662064329429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 499534995551004441376219619 749302493326506662064329429)
              ·
                refine ⟨17561777187339999892132721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 749302493326506662064329429 17561777187339999892132721)
                ·
                  refine ⟨13171332890504999919099541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17561777187339999892132721 13171332890504999919099541)
                  ·
                    refine ⟨617406229242421871207791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13171332890504999919099541 617406229242421871207791)
                    ·
                      rfl

theorem cell23_3607183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 2, 6].length) (baseStart_3607183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3607183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3607183 prefixEnd_3607183 := by exact prefixLift 3607183
  have htrace : WordTrace (prefixWord ++ tailWord_3607183) baseStart_3607183 baseEnd_3607183 := by
    simpa [prefixWord, tailWord_3607183, baseEnd_3607183] using wordTrace_append hprefix tailTrace_3607183
  have hstable : (prefixWord ++ tailWord_3607183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607183).length < 2 ^ (prefixWord ++ tailWord_3607183).sum := by decide
  have hdescent : baseEnd_3607183 < baseStart_3607183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607277 : List Nat := [1, 5, 1, 2, 1, 1, 3, 2, 2, 5]
def baseStart_3607277 : Nat := 118140960795 + 3607277 * 2 ^ 59
def prefixEnd_3607277 : Nat := 4983230072969 + 3 ^ 40 * 3607277 * 2
def baseEnd_3607277 : Nat := 617422318302929415282647

theorem tailTrace_3607277 : CollatzResearch.WordTrace tailWord_3607277 prefixEnd_3607277 617422318302929415282647 := by
  unfold tailWord_3607277
  simp only [CollatzResearch.WordTrace]
  refine ⟨131568200952458977708564085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87712133968305985139042723 131568200952458977708564085)
  ·
    refine ⟨12334518839293029160177883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 131568200952458977708564085 12334518839293029160177883)
    ·
      refine ⟨18501778258939543740266825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12334518839293029160177883 18501778258939543740266825)
      ·
        refine ⟨13876333694204657805200119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18501778258939543740266825 13876333694204657805200119)
        ·
          refine ⟨20814500541306986707800179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13876333694204657805200119 20814500541306986707800179)
          ·
            refine ⟨31221750811960480061700269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20814500541306986707800179 31221750811960480061700269)
            ·
              refine ⟨11708156554485180023137601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31221750811960480061700269 11708156554485180023137601)
              ·
                refine ⟨8781117415863885017353201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11708156554485180023137601 8781117415863885017353201)
                ·
                  refine ⟨6585838061897913763014901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8781117415863885017353201 6585838061897913763014901)
                  ·
                    refine ⟨617422318302929415282647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6585838061897913763014901 617422318302929415282647)
                    ·
                      rfl

theorem cell23_3607277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_3607277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3607277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3607277 prefixEnd_3607277 := by exact prefixLift 3607277
  have htrace : WordTrace (prefixWord ++ tailWord_3607277) baseStart_3607277 baseEnd_3607277 := by
    simpa [prefixWord, tailWord_3607277, baseEnd_3607277] using wordTrace_append hprefix tailTrace_3607277
  have hstable : (prefixWord ++ tailWord_3607277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607277).length < 2 ^ (prefixWord ++ tailWord_3607277).sum := by decide
  have hdescent : baseEnd_3607277 < baseStart_3607277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607297 : List Nat := [1, 2, 4, 1, 1, 1, 1, 3, 1, 6, 2]
def baseStart_3607297 : Nat := 118140960795 + 3607297 * 2 ^ 59
def prefixEnd_3607297 : Nat := 4983230072969 + 3 ^ 40 * 3607297 * 2
def baseEnd_3607297 : Nat := 1852277224521878167597849

theorem tailTrace_3607297 : CollatzResearch.WordTrace tailWord_3607297 prefixEnd_3607297 1852277224521878167597849 := by
  unfold tailWord_3607297
  simp only [CollatzResearch.WordTrace]
  refine ⟨131568930412386521124292145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87712620274924347416194763 131568930412386521124292145)
  ·
    refine ⟨98676697809289890843219109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131568930412386521124292145 98676697809289890843219109)
    ·
      refine ⟨18501880839241854533103583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98676697809289890843219109 18501880839241854533103583)
      ·
        refine ⟨27752821258862781799655375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18501880839241854533103583 27752821258862781799655375)
        ·
          refine ⟨41629231888294172699483063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27752821258862781799655375 41629231888294172699483063)
          ·
            refine ⟨62443847832441259049224595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41629231888294172699483063 62443847832441259049224595)
            ·
              refine ⟨93665771748661888573836893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62443847832441259049224595 93665771748661888573836893)
              ·
                refine ⟨35124664405748208215188835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93665771748661888573836893 35124664405748208215188835)
                ·
                  refine ⟨52686996608622312322783253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35124664405748208215188835 52686996608622312322783253)
                  ·
                    refine ⟨2469702966029170890130465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 52686996608622312322783253 2469702966029170890130465)
                    ·
                      refine ⟨1852277224521878167597849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2469702966029170890130465 1852277224521878167597849)
                      ·
                        rfl

theorem cell23_3607297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 6, 2].length) (baseStart_3607297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3607297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3607297 prefixEnd_3607297 := by exact prefixLift 3607297
  have htrace : WordTrace (prefixWord ++ tailWord_3607297) baseStart_3607297 baseEnd_3607297 := by
    simpa [prefixWord, tailWord_3607297, baseEnd_3607297] using wordTrace_append hprefix tailTrace_3607297
  have hstable : (prefixWord ++ tailWord_3607297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607297).length < 2 ^ (prefixWord ++ tailWord_3607297).sum := by decide
  have hdescent : baseEnd_3607297 < baseStart_3607297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607310 : List Nat := [4, 1, 1, 2, 1, 1, 1, 2, 1, 3, 6]
def baseStart_3607310 : Nat := 118140960795 + 3607310 * 2 ^ 59
def prefixEnd_3607310 : Nat := 4983230072969 + 3 ^ 40 * 3607310 * 2
def baseEnd_3607310 : Nat := 1852283899770386616735289

theorem tailTrace_3607310 : CollatzResearch.WordTrace tailWord_3607310 prefixEnd_3607310 1852283899770386616735289 := by
  unfold tailWord_3607310
  simp only [CollatzResearch.WordTrace]
  refine ⟨16446175570167428043064423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87712936374226282896343589 16446175570167428043064423)
  ·
    refine ⟨24669263355251142064596635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16446175570167428043064423 24669263355251142064596635)
    ·
      refine ⟨37003895032876713096894953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24669263355251142064596635 37003895032876713096894953)
      ·
        refine ⟨27752921274657534822671215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37003895032876713096894953 27752921274657534822671215)
        ·
          refine ⟨41629381911986302234006823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27752921274657534822671215 41629381911986302234006823)
          ·
            refine ⟨62444072867979453351010235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41629381911986302234006823 62444072867979453351010235)
            ·
              refine ⟨93666109301969180026515353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62444072867979453351010235 93666109301969180026515353)
              ·
                refine ⟨70249581976476885019886515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93666109301969180026515353 70249581976476885019886515)
                ·
                  refine ⟨105374372964715327529829773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70249581976476885019886515 105374372964715327529829773)
                  ·
                    refine ⟨39515389861768247823686165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 105374372964715327529829773 39515389861768247823686165)
                    ·
                      refine ⟨1852283899770386616735289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39515389861768247823686165 1852283899770386616735289)
                      ·
                        rfl

theorem cell23_3607310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_3607310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3607310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3607310 prefixEnd_3607310 := by exact prefixLift 3607310
  have htrace : WordTrace (prefixWord ++ tailWord_3607310) baseStart_3607310 baseEnd_3607310 := by
    simpa [prefixWord, tailWord_3607310, baseEnd_3607310] using wordTrace_append hprefix tailTrace_3607310
  have hstable : (prefixWord ++ tailWord_3607310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607310).length < 2 ^ (prefixWord ++ tailWord_3607310).sum := by decide
  have hdescent : baseEnd_3607310 < baseStart_3607310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607340 : List Nat := [2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 6]
def baseStart_3607340 : Nat := 118140960795 + 3607340 * 2 ^ 59
def prefixEnd_3607340 : Nat := 4983230072969 + 3 ^ 40 * 3607340 * 2
def baseEnd_3607340 : Nat := 1852299304190021499360151

theorem tailTrace_3607340 : CollatzResearch.WordTrace tailWord_3607340 prefixEnd_3607340 1852299304190021499360151 := by
  unfold tailWord_3607340
  simp only [CollatzResearch.WordTrace]
  refine ⟨65785249375615369734053737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87713665834153826312071649 65785249375615369734053737)
  ·
    refine ⟨49338937031711527300540303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65785249375615369734053737 49338937031711527300540303)
    ·
      refine ⟨74008405547567290950810455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49338937031711527300540303 74008405547567290950810455)
      ·
        refine ⟨111012608321350936426215683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74008405547567290950810455 111012608321350936426215683)
        ·
          refine ⟨166518912482026404639323525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111012608321350936426215683 166518912482026404639323525)
          ·
            refine ⟨31222296090379950869873161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 166518912482026404639323525 31222296090379950869873161)
            ·
              refine ⟨23416722067784963152404871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31222296090379950869873161 23416722067784963152404871)
              ·
                refine ⟨35125083101677444728607307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23416722067784963152404871 35125083101677444728607307)
                ·
                  refine ⟨52687624652516167092910961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35125083101677444728607307 52687624652516167092910961)
                  ·
                    refine ⟨39515718489387125319683221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52687624652516167092910961 39515718489387125319683221)
                    ·
                      refine ⟨1852299304190021499360151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39515718489387125319683221 1852299304190021499360151)
                      ·
                        rfl

theorem cell23_3607340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 6].length) (baseStart_3607340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3607340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3607340 prefixEnd_3607340 := by exact prefixLift 3607340
  have htrace : WordTrace (prefixWord ++ tailWord_3607340) baseStart_3607340 baseEnd_3607340 := by
    simpa [prefixWord, tailWord_3607340, baseEnd_3607340] using wordTrace_append hprefix tailTrace_3607340
  have hstable : (prefixWord ++ tailWord_3607340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607340).length < 2 ^ (prefixWord ++ tailWord_3607340).sum := by decide
  have hdescent : baseEnd_3607340 < baseStart_3607340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607367 : List Nat := [1, 1, 4, 1, 2, 1, 1, 6, 1, 5]
def baseStart_3607367 : Nat := 118140960795 + 3607367 * 2 ^ 59
def prefixEnd_3607367 : Nat := 4983230072969 + 3 ^ 40 * 3607367 * 2
def baseEnd_3607367 : Nat := 617437722722564297907509

theorem tailTrace_3607367 : CollatzResearch.WordTrace tailWord_3607367 prefixEnd_3607367 617437722722564297907509 := by
  unfold tailWord_3607367
  simp only [CollatzResearch.WordTrace]
  refine ⟨131571483522132923079340355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87714322348088615386226903 131571483522132923079340355)
  ·
    refine ⟨197357225283199384619010533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131571483522132923079340355 197357225283199384619010533)
    ·
      refine ⟨37004479740599884616064475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 197357225283199384619010533 37004479740599884616064475)
      ·
        refine ⟨55506719610899826924096713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37004479740599884616064475 55506719610899826924096713)
        ·
          refine ⟨41630039708174870193072535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55506719610899826924096713 41630039708174870193072535)
          ·
            refine ⟨62445059562262305289608803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41630039708174870193072535 62445059562262305289608803)
            ·
              refine ⟨93667589343393457934413205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62445059562262305289608803 93667589343393457934413205)
              ·
                refine ⟨4390668250471568340675619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 93667589343393457934413205 4390668250471568340675619)
                ·
                  refine ⟨6586002375707352511013429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4390668250471568340675619 6586002375707352511013429)
                  ·
                    refine ⟨617437722722564297907509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6586002375707352511013429 617437722722564297907509)
                    ·
                      rfl

theorem cell23_3607367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 6, 1, 5].length) (baseStart_3607367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3607367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3607367 prefixEnd_3607367 := by exact prefixLift 3607367
  have htrace : WordTrace (prefixWord ++ tailWord_3607367) baseStart_3607367 baseEnd_3607367 := by
    simpa [prefixWord, tailWord_3607367, baseEnd_3607367] using wordTrace_append hprefix tailTrace_3607367
  have hstable : (prefixWord ++ tailWord_3607367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607367).length < 2 ^ (prefixWord ++ tailWord_3607367).sum := by decide
  have hdescent : baseEnd_3607367 < baseStart_3607367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607407 : List Nat := [1, 1, 2, 1, 3, 1, 1, 3, 5, 2, 3]
def baseStart_3607407 : Nat := 118140960795 + 3607407 * 2 ^ 59
def prefixEnd_3607407 : Nat := 4983230072969 + 3 ^ 40 * 3607407 * 2
def baseEnd_3607407 : Nat := 1852333707393872737222343

theorem tailTrace_3607407 : CollatzResearch.WordTrace tailWord_3607407 prefixEnd_3607407 1852333707393872737222343 := by
  unfold tailWord_3607407
  simp only [CollatzResearch.WordTrace]
  refine ⟨131572942441988009910796475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87715294961325339940530983 131572942441988009910796475)
  ·
    refine ⟨197359413662982014866194713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131572942441988009910796475 197359413662982014866194713)
    ·
      refine ⟨148019560247236511149646035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197359413662982014866194713 148019560247236511149646035)
      ·
        refine ⟨222029340370854766724469053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148019560247236511149646035 222029340370854766724469053)
        ·
          refine ⟨83261002639070537521675895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222029340370854766724469053 83261002639070537521675895)
          ·
            refine ⟨124891503958605806282513843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83261002639070537521675895 124891503958605806282513843)
            ·
              refine ⟨187337255937908709423770765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124891503958605806282513843 187337255937908709423770765)
              ·
                refine ⟨70251470976715766033914037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 187337255937908709423770765 70251470976715766033914037)
                ·
                  refine ⟨6586075404067103065679441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70251470976715766033914037 6586075404067103065679441)
                  ·
                    refine ⟨4939556553050327299259581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6586075404067103065679441 4939556553050327299259581)
                    ·
                      refine ⟨1852333707393872737222343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4939556553050327299259581 1852333707393872737222343)
                      ·
                        rfl

theorem cell23_3607407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 5, 2, 3].length) (baseStart_3607407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3607407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3607407 prefixEnd_3607407 := by exact prefixLift 3607407
  have htrace : WordTrace (prefixWord ++ tailWord_3607407) baseStart_3607407 baseEnd_3607407 := by
    simpa [prefixWord, tailWord_3607407, baseEnd_3607407] using wordTrace_append hprefix tailTrace_3607407
  have hstable : (prefixWord ++ tailWord_3607407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607407).length < 2 ^ (prefixWord ++ tailWord_3607407).sum := by decide
  have hdescent : baseEnd_3607407 < baseStart_3607407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607417 : List Nat := [1, 2, 1, 3, 2, 4, 1, 1, 1, 1, 6]
def baseStart_3607417 : Nat := 118140960795 + 3607417 * 2 ^ 59
def prefixEnd_3607417 : Nat := 4983230072969 + 3 ^ 40 * 3607417 * 2
def baseEnd_3607417 : Nat := 1852338842200417698097297

theorem tailTrace_3607417 : CollatzResearch.WordTrace tailWord_3607417 prefixEnd_3607417 1852338842200417698097297 := by
  unfold tailWord_3607417
  simp only [CollatzResearch.WordTrace]
  refine ⟨131573307171951781618660505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87715538114634521079107003 131573307171951781618660505)
  ·
    refine ⟨98679980378963836213995379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131573307171951781618660505 98679980378963836213995379)
    ·
      refine ⟨148019970568445754320993069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98679980378963836213995379 148019970568445754320993069)
      ·
        refine ⟨55507488963167157870372401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148019970568445754320993069 55507488963167157870372401)
        ·
          refine ⟨41630616722375368402779301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55507488963167157870372401 41630616722375368402779301)
          ·
            refine ⟨7805740635445381575521119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41630616722375368402779301 7805740635445381575521119)
            ·
              refine ⟨11708610953168072363281679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7805740635445381575521119 11708610953168072363281679)
              ·
                refine ⟨17562916429752108544922519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11708610953168072363281679 17562916429752108544922519)
                ·
                  refine ⟨26344374644628162817383779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17562916429752108544922519 26344374644628162817383779)
                  ·
                    refine ⟨39516561966942244226075669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26344374644628162817383779 39516561966942244226075669)
                    ·
                      refine ⟨1852338842200417698097297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39516561966942244226075669 1852338842200417698097297)
                      ·
                        rfl

theorem cell23_3607417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 1, 6].length) (baseStart_3607417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3607417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3607417 prefixEnd_3607417 := by exact prefixLift 3607417
  have htrace : WordTrace (prefixWord ++ tailWord_3607417) baseStart_3607417 baseEnd_3607417 := by
    simpa [prefixWord, tailWord_3607417, baseEnd_3607417] using wordTrace_append hprefix tailTrace_3607417
  have hstable : (prefixWord ++ tailWord_3607417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607417).length < 2 ^ (prefixWord ++ tailWord_3607417).sum := by decide
  have hdescent : baseEnd_3607417 < baseStart_3607417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607421 : List Nat := [1, 4, 1, 1, 2, 1, 4, 2, 3, 2, 2]
def baseStart_3607421 : Nat := 118140960795 + 3607421 * 2 ^ 59
def prefixEnd_3607421 : Nat := 4983230072969 + 3 ^ 40 * 3607421 * 2
def baseEnd_3607421 : Nat := 1852340896123035682447279

theorem tailTrace_3607421 : CollatzResearch.WordTrace tailWord_3607421 prefixEnd_3607421 1852340896123035682447279 := by
  unfold tailWord_3607421
  simp only [CollatzResearch.WordTrace]
  refine ⟨131573453063937290301806117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87715635375958193534537411 131573453063937290301806117)
  ·
    refine ⟨24670022449488241931588647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131573453063937290301806117 24670022449488241931588647)
    ·
      refine ⟨37005033674232362897382971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24670022449488241931588647 37005033674232362897382971)
      ·
        refine ⟨55507550511348544346074457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37005033674232362897382971 55507550511348544346074457)
        ·
          refine ⟨41630662883511408259555843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55507550511348544346074457 41630662883511408259555843)
          ·
            refine ⟨62445994325267112389333765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41630662883511408259555843 62445994325267112389333765)
            ·
              refine ⟨11708623935987583573000081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62445994325267112389333765 11708623935987583573000081)
              ·
                refine ⟨8781467951990687679750061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11708623935987583573000081 8781467951990687679750061)
                ·
                  refine ⟨3293050481996507879906273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8781467951990687679750061 3293050481996507879906273)
                  ·
                    refine ⟨2469787861497380909929705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3293050481996507879906273 2469787861497380909929705)
                    ·
                      refine ⟨1852340896123035682447279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2469787861497380909929705 1852340896123035682447279)
                      ·
                        rfl

theorem cell23_3607421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 2, 3, 2, 2].length) (baseStart_3607421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3607421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3607421 prefixEnd_3607421 := by exact prefixLift 3607421
  have htrace : WordTrace (prefixWord ++ tailWord_3607421) baseStart_3607421 baseEnd_3607421 := by
    simpa [prefixWord, tailWord_3607421, baseEnd_3607421] using wordTrace_append hprefix tailTrace_3607421
  have hstable : (prefixWord ++ tailWord_3607421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607421).length < 2 ^ (prefixWord ++ tailWord_3607421).sum := by decide
  have hdescent : baseEnd_3607421 < baseStart_3607421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607481 : List Nat := [1, 2, 1, 4, 2, 3, 1, 1, 3, 3, 2]
def baseStart_3607481 : Nat := 118140960795 + 3607481 * 2 ^ 59
def prefixEnd_3607481 : Nat := 4983230072969 + 3 ^ 40 * 3607481 * 2
def baseEnd_3607481 : Nat := 1852371704962305447697003

theorem tailTrace_3607481 : CollatzResearch.WordTrace tailWord_3607481 prefixEnd_3607481 1852371704962305447697003 := by
  unfold tailWord_3607481
  simp only [CollatzResearch.WordTrace]
  refine ⟨131575641443719920548990297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87717094295813280365993531 131575641443719920548990297)
  ·
    refine ⟨98681731082789940411742723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131575641443719920548990297 98681731082789940411742723)
    ·
      refine ⟨148022596624184910617614085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98681731082789940411742723 148022596624184910617614085)
      ·
        refine ⟨27754236867034670740802641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148022596624184910617614085 27754236867034670740802641)
        ·
          refine ⟨20815677650276003055601981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27754236867034670740802641 20815677650276003055601981)
          ·
            refine ⟨7805879118853501145850743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20815677650276003055601981 7805879118853501145850743)
            ·
              refine ⟨11708818678280251718776115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7805879118853501145850743 11708818678280251718776115)
              ·
                refine ⟨17563228017420377578164173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11708818678280251718776115 17563228017420377578164173)
                ·
                  refine ⟨6586210506532641591811565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17563228017420377578164173 6586210506532641591811565)
                  ·
                    refine ⟨2469828939949740596929337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6586210506532641591811565 2469828939949740596929337)
                    ·
                      refine ⟨1852371704962305447697003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2469828939949740596929337 1852371704962305447697003)
                      ·
                        rfl

theorem cell23_3607481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 3, 3, 2].length) (baseStart_3607481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3607481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3607481 prefixEnd_3607481 := by exact prefixLift 3607481
  have htrace : WordTrace (prefixWord ++ tailWord_3607481) baseStart_3607481 baseEnd_3607481 := by
    simpa [prefixWord, tailWord_3607481, baseEnd_3607481] using wordTrace_append hprefix tailTrace_3607481
  have hstable : (prefixWord ++ tailWord_3607481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607481).length < 2 ^ (prefixWord ++ tailWord_3607481).sum := by decide
  have hdescent : baseEnd_3607481 < baseStart_3607481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607497 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 3, 6, 3]
def baseStart_3607497 : Nat := 118140960795 + 3607497 * 2 ^ 59
def prefixEnd_3607497 : Nat := 4983230072969 + 3 ^ 40 * 3607497 * 2
def baseEnd_3607497 : Nat := 1852379920652777385096929

theorem tailTrace_3607497 : CollatzResearch.WordTrace tailWord_3607497 prefixEnd_3607497 1852379920652777385096929 := by
  unfold tailWord_3607497
  simp only [CollatzResearch.WordTrace]
  refine ⟨131576225011661955281572745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87717483341107970187715163 131576225011661955281572745)
  ·
    refine ⟨98682168758746466461179559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131576225011661955281572745 98682168758746466461179559)
    ·
      refine ⟨148023253138119699691769339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98682168758746466461179559 148023253138119699691769339)
      ·
        refine ⟨222034879707179549537654009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148023253138119699691769339 222034879707179549537654009)
        ·
          refine ⟨166526159780384662153240507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222034879707179549537654009 166526159780384662153240507)
          ·
            refine ⟨249789239670576993229860761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166526159780384662153240507 249789239670576993229860761)
            ·
              refine ⟨187341929752932744922395571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 249789239670576993229860761 187341929752932744922395571)
              ·
                refine ⟨281012894629399117383593357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187341929752932744922395571 281012894629399117383593357)
                ·
                  refine ⟨105379835486024669018847509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 281012894629399117383593357 105379835486024669018847509)
                  ·
                    refine ⟨4939679788407406360258477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 105379835486024669018847509 4939679788407406360258477)
                    ·
                      refine ⟨1852379920652777385096929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4939679788407406360258477 1852379920652777385096929)
                      ·
                        rfl

theorem cell23_3607497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 6, 3].length) (baseStart_3607497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3607497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3607497 prefixEnd_3607497 := by exact prefixLift 3607497
  have htrace : WordTrace (prefixWord ++ tailWord_3607497) baseStart_3607497 baseEnd_3607497 := by
    simpa [prefixWord, tailWord_3607497, baseEnd_3607497] using wordTrace_append hprefix tailTrace_3607497
  have hstable : (prefixWord ++ tailWord_3607497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607497).length < 2 ^ (prefixWord ++ tailWord_3607497).sum := by decide
  have hdescent : baseEnd_3607497 < baseStart_3607497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607514 : List Nat := [3, 1, 1, 2, 4, 1, 1, 1, 2, 4, 3]
def baseStart_3607514 : Nat := 118140960795 + 3607514 * 2 ^ 59
def prefixEnd_3607514 : Nat := 4983230072969 + 3 ^ 40 * 3607514 * 2
def baseEnd_3607514 : Nat := 1852388649823903818584351

theorem tailTrace_3607514 : CollatzResearch.WordTrace tailWord_3607514 prefixEnd_3607514 1852388649823903818584351 := by
  unfold tailWord_3607514
  simp only [CollatzResearch.WordTrace]
  refine ⟨32894211263150091796235399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87717896701733578123294397 32894211263150091796235399)
  ·
    refine ⟨49341316894725137694353099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32894211263150091796235399 49341316894725137694353099)
    ·
      refine ⟨74011975342087706541529649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49341316894725137694353099 74011975342087706541529649)
      ·
        refine ⟨55508981506565779906147237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74011975342087706541529649 55508981506565779906147237)
        ·
          refine ⟨10407934032481083732402607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55508981506565779906147237 10407934032481083732402607)
          ·
            refine ⟨15611901048721625598603911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10407934032481083732402607 15611901048721625598603911)
            ·
              refine ⟨23417851573082438397905867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15611901048721625598603911 23417851573082438397905867)
              ·
                refine ⟨35126777359623657596858801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23417851573082438397905867 35126777359623657596858801)
                ·
                  refine ⟨26345083019717743197644101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35126777359623657596858801 26345083019717743197644101)
                  ·
                    refine ⟨4939703066197076849558269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26345083019717743197644101 4939703066197076849558269)
                    ·
                      refine ⟨1852388649823903818584351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4939703066197076849558269 1852388649823903818584351)
                      ·
                        rfl

theorem cell23_3607514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 2, 4, 3].length) (baseStart_3607514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3607514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3607514 prefixEnd_3607514 := by exact prefixLift 3607514
  have htrace : WordTrace (prefixWord ++ tailWord_3607514) baseStart_3607514 baseEnd_3607514 := by
    simpa [prefixWord, tailWord_3607514, baseEnd_3607514] using wordTrace_append hprefix tailTrace_3607514
  have hstable : (prefixWord ++ tailWord_3607514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607514).length < 2 ^ (prefixWord ++ tailWord_3607514).sum := by decide
  have hdescent : baseEnd_3607514 < baseStart_3607514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607528 : List Nat := [2, 1, 4, 1, 1, 1, 4, 3, 2, 2, 2]
def baseStart_3607528 : Nat := 118140960795 + 3607528 * 2 ^ 59
def prefixEnd_3607528 : Nat := 4983230072969 + 3 ^ 40 * 3607528 * 2
def baseEnd_3607528 : Nat := 1852395838553066763809287

theorem tailTrace_3607528 : CollatzResearch.WordTrace tailWord_3607528 prefixEnd_3607528 1852395838553066763809287 := by
  unfold tailWord_3607528
  simp only [CollatzResearch.WordTrace]
  refine ⟨65788677837274823787975619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87718237116366431717300825 65788677837274823787975619)
  ·
    refine ⟨98683016755912235681963429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65788677837274823787975619 98683016755912235681963429)
    ·
      refine ⟨18503065641733544190368143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98683016755912235681963429 18503065641733544190368143)
      ·
        refine ⟨27754598462600316285552215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18503065641733544190368143 27754598462600316285552215)
        ·
          refine ⟨41631897693900474428328323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27754598462600316285552215 41631897693900474428328323)
          ·
            refine ⟨62447846540850711642492485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41631897693900474428328323 62447846540850711642492485)
            ·
              refine ⟨11708971226409508432967341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62447846540850711642492485 11708971226409508432967341)
              ·
                refine ⟨4390864209903565662362753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11708971226409508432967341 4390864209903565662362753)
                ·
                  refine ⟨3293148157427674246772065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4390864209903565662362753 3293148157427674246772065)
                  ·
                    refine ⟨2469861118070755685079049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3293148157427674246772065 2469861118070755685079049)
                    ·
                      refine ⟨1852395838553066763809287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2469861118070755685079049 1852395838553066763809287)
                      ·
                        rfl

theorem cell23_3607528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 3, 2, 2, 2].length) (baseStart_3607528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3607528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3607528 prefixEnd_3607528 := by exact prefixLift 3607528
  have htrace : WordTrace (prefixWord ++ tailWord_3607528) baseStart_3607528 baseEnd_3607528 := by
    simpa [prefixWord, tailWord_3607528, baseEnd_3607528] using wordTrace_append hprefix tailTrace_3607528
  have hstable : (prefixWord ++ tailWord_3607528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607528).length < 2 ^ (prefixWord ++ tailWord_3607528).sum := by decide
  have hdescent : baseEnd_3607528 < baseStart_3607528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607567 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 2, 7, 4]
def baseStart_3607567 : Nat := 118140960795 + 3607567 * 2 ^ 59
def prefixEnd_3607567 : Nat := 4983230072969 + 3 ^ 40 * 3607567 * 2
def baseEnd_3607567 : Nat := 1852415864298592111221607

theorem tailTrace_3607567 : CollatzResearch.WordTrace tailWord_3607567 prefixEnd_3607567 1852415864298592111221607 := by
  unfold tailWord_3607567
  simp only [CollatzResearch.WordTrace]
  refine ⟨131578778121408357236620955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87719185414272238157747303 131578778121408357236620955)
  ·
    refine ⟨197368167182112535854931433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131578778121408357236620955 197368167182112535854931433)
    ·
      refine ⟨148026125386584401891198575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197368167182112535854931433 148026125386584401891198575)
      ·
        refine ⟨222039188079876602836797863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148026125386584401891198575 222039188079876602836797863)
        ·
          refine ⟨333058782119814904255196795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222039188079876602836797863 333058782119814904255196795)
          ·
            refine ⟨499588173179722356382795193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333058782119814904255196795 499588173179722356382795193)
            ·
              refine ⟨374691129884791767287096395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 499588173179722356382795193 374691129884791767287096395)
              ·
                refine ⟨562036694827187650930644593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 374691129884791767287096395 562036694827187650930644593)
                ·
                  refine ⟨421527521120390738197983445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 562036694827187650930644593 421527521120390738197983445)
                  ·
                    refine ⟨9879551276259157926515237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 421527521120390738197983445 9879551276259157926515237)
                    ·
                      refine ⟨1852415864298592111221607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9879551276259157926515237 1852415864298592111221607)
                      ·
                        rfl

theorem cell23_3607567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 7, 4].length) (baseStart_3607567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3607567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3607567 prefixEnd_3607567 := by exact prefixLift 3607567
  have htrace : WordTrace (prefixWord ++ tailWord_3607567) baseStart_3607567 baseEnd_3607567 := by
    simpa [prefixWord, tailWord_3607567, baseEnd_3607567] using wordTrace_append hprefix tailTrace_3607567
  have hstable : (prefixWord ++ tailWord_3607567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607567).length < 2 ^ (prefixWord ++ tailWord_3607567).sum := by decide
  have hdescent : baseEnd_3607567 < baseStart_3607567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607624 : List Nat := [2, 1, 3, 1, 1, 1, 4, 4, 6]
def baseStart_3607624 : Nat := 118140960795 + 3607624 * 2 ^ 59
def prefixEnd_3607624 : Nat := 4983230072969 + 3 ^ 40 * 3607624 * 2
def baseEnd_3607624 : Nat := 205827236966210932023205

theorem tailTrace_3607624 : CollatzResearch.WordTrace tailWord_3607624 prefixEnd_3607624 205827236966210932023205 := by
  unfold tailWord_3607624
  simp only [CollatzResearch.WordTrace]
  refine ⟨65790428541100927985722963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87720571388134570647630617 65790428541100927985722963)
  ·
    refine ⟨98685642811651391978584445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65790428541100927985722963 98685642811651391978584445)
    ·
      refine ⟨37007116054369271991969167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98685642811651391978584445 37007116054369271991969167)
      ·
        refine ⟨55510674081553907987953751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37007116054369271991969167 55510674081553907987953751)
        ·
          refine ⟨83266011122330861981930627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55510674081553907987953751 83266011122330861981930627)
          ·
            refine ⟨124899016683496292972895941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83266011122330861981930627 124899016683496292972895941)
            ·
              refine ⟨23418565628155554932417989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124899016683496292972895941 23418565628155554932417989)
              ·
                refine ⟨4390981055279166549828373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23418565628155554932417989 4390981055279166549828373)
                ·
                  refine ⟨205827236966210932023205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4390981055279166549828373 205827236966210932023205)
                  ·
                    rfl

theorem cell23_3607624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 4, 6].length) (baseStart_3607624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3607624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3607624 prefixEnd_3607624 := by exact prefixLift 3607624
  have htrace : WordTrace (prefixWord ++ tailWord_3607624) baseStart_3607624 baseEnd_3607624 := by
    simpa [prefixWord, tailWord_3607624, baseEnd_3607624] using wordTrace_append hprefix tailTrace_3607624
  have hstable : (prefixWord ++ tailWord_3607624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607624).length < 2 ^ (prefixWord ++ tailWord_3607624).sum := by decide
  have hdescent : baseEnd_3607624 < baseStart_3607624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607651 : List Nat := [1, 1, 1, 5, 1, 1, 1, 3, 5, 1, 3]
def baseStart_3607651 : Nat := 118140960795 + 3607651 * 2 ^ 59
def prefixEnd_3607651 : Nat := 4983230072969 + 3 ^ 40 * 3607651 * 2
def baseEnd_3607651 : Nat := 1852458996673569782571221

theorem tailTrace_3607651 : CollatzResearch.WordTrace tailWord_3607651 prefixEnd_3607651 1852458996673569782571221 := by
  unfold tailWord_3607651
  simp only [CollatzResearch.WordTrace]
  refine ⟨131581841853104039582678807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87721227902069359721785871 131581841853104039582678807)
  ·
    refine ⟨197372762779656059374018211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131581841853104039582678807 197372762779656059374018211)
    ·
      refine ⟨296059144169484089061027317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197372762779656059374018211 296059144169484089061027317)
      ·
        refine ⟨27755544765889133349471311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 296059144169484089061027317 27755544765889133349471311)
        ·
          refine ⟨41633317148833700024206967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27755544765889133349471311 41633317148833700024206967)
          ·
            refine ⟨62449975723250550036310451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41633317148833700024206967 62449975723250550036310451)
            ·
              refine ⟨93674963584875825054465677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62449975723250550036310451 93674963584875825054465677)
              ·
                refine ⟨35128111344328434395424629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93674963584875825054465677 35128111344328434395424629)
                ·
                  refine ⟨3293260438530790724571059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35128111344328434395424629 3293260438530790724571059)
                  ·
                    refine ⟨4939890657796186086856589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3293260438530790724571059 4939890657796186086856589)
                    ·
                      refine ⟨1852458996673569782571221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4939890657796186086856589 1852458996673569782571221)
                      ·
                        rfl

theorem cell23_3607651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 5, 1, 3].length) (baseStart_3607651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3607651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3607651 prefixEnd_3607651 := by exact prefixLift 3607651
  have htrace : WordTrace (prefixWord ++ tailWord_3607651) baseStart_3607651 baseEnd_3607651 := by
    simpa [prefixWord, tailWord_3607651, baseEnd_3607651] using wordTrace_append hprefix tailTrace_3607651
  have hstable : (prefixWord ++ tailWord_3607651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607651).length < 2 ^ (prefixWord ++ tailWord_3607651).sum := by decide
  have hdescent : baseEnd_3607651 < baseStart_3607651 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607722 : List Nat := [3, 1, 5, 1, 1, 3, 2, 1, 1, 5]
def baseStart_3607722 : Nat := 118140960795 + 3607722 * 2 ^ 59
def prefixEnd_3607722 : Nat := 4983230072969 + 3 ^ 40 * 3607722 * 2
def baseEnd_3607722 : Nat := 617498484600013001594465

theorem tailTrace_3607722 : CollatzResearch.WordTrace tailWord_3607722 prefixEnd_3607722 617498484600013001594465 := by
  unfold tailWord_3607722
  simp only [CollatzResearch.WordTrace]
  refine ⟨32896107858961704677128355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87722954290564545805675613 32896107858961704677128355)
  ·
    refine ⟨49344161788442557015692533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32896107858961704677128355 49344161788442557015692533)
    ·
      refine ⟨4626015167666489720221175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49344161788442557015692533 4626015167666489720221175)
      ·
        refine ⟨6939022751499734580331763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4626015167666489720221175 6939022751499734580331763)
        ·
          refine ⟨10408534127249601870497645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6939022751499734580331763 10408534127249601870497645)
          ·
            refine ⟨3903200297718600701436617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10408534127249601870497645 3903200297718600701436617)
            ·
              refine ⟨2927400223288950526077463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3903200297718600701436617 2927400223288950526077463)
              ·
                refine ⟨4391100334933425789116195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2927400223288950526077463 4391100334933425789116195)
                ·
                  refine ⟨6586650502400138683674293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4391100334933425789116195 6586650502400138683674293)
                  ·
                    refine ⟨617498484600013001594465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6586650502400138683674293 617498484600013001594465)
                    ·
                      rfl

theorem cell23_3607722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_3607722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3607722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3607722 prefixEnd_3607722 := by exact prefixLift 3607722
  have htrace : WordTrace (prefixWord ++ tailWord_3607722) baseStart_3607722 baseEnd_3607722 := by
    simpa [prefixWord, tailWord_3607722, baseEnd_3607722] using wordTrace_append hprefix tailTrace_3607722
  have hstable : (prefixWord ++ tailWord_3607722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607722).length < 2 ^ (prefixWord ++ tailWord_3607722).sum := by decide
  have hdescent : baseEnd_3607722 < baseStart_3607722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607725 : List Nat := [1, 5, 2, 1, 3, 1, 1, 3, 1, 1, 4]
def baseStart_3607725 : Nat := 118140960795 + 3607725 * 2 ^ 59
def prefixEnd_3607725 : Nat := 4983230072969 + 3 ^ 40 * 3607725 * 2
def baseEnd_3607725 : Nat := 1852496994242002493045881

theorem tailTrace_3607725 : CollatzResearch.WordTrace tailWord_3607725 prefixEnd_3607725 1852496994242002493045881 := by
  unfold tailWord_3607725
  simp only [CollatzResearch.WordTrace]
  refine ⟨131584540854835950220872629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87723027236557300147248419 131584540854835950220872629)
  ·
    refine ⟨12336050705140870333206809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 131584540854835950220872629 12336050705140870333206809)
    ·
      refine ⟨9252038028855652749905107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12336050705140870333206809 9252038028855652749905107)
      ·
        refine ⟨13878057043283479124857661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9252038028855652749905107 13878057043283479124857661)
        ·
          refine ⟨5204271391231304671821623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13878057043283479124857661 5204271391231304671821623)
          ·
            refine ⟨7806407086846957007732435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5204271391231304671821623 7806407086846957007732435)
            ·
              refine ⟨11709610630270435511598653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7806407086846957007732435 11709610630270435511598653)
              ·
                refine ⟨4391103986351413316849495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11709610630270435511598653 4391103986351413316849495)
                ·
                  refine ⟨6586655979527119975274243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4391103986351413316849495 6586655979527119975274243)
                  ·
                    refine ⟨9879983969290679962911365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6586655979527119975274243 9879983969290679962911365)
                    ·
                      refine ⟨1852496994242002493045881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9879983969290679962911365 1852496994242002493045881)
                      ·
                        rfl

theorem cell23_3607725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_3607725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3607725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3607725 prefixEnd_3607725 := by exact prefixLift 3607725
  have htrace : WordTrace (prefixWord ++ tailWord_3607725) baseStart_3607725 baseEnd_3607725 := by
    simpa [prefixWord, tailWord_3607725, baseEnd_3607725] using wordTrace_append hprefix tailTrace_3607725
  have hstable : (prefixWord ++ tailWord_3607725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607725).length < 2 ^ (prefixWord ++ tailWord_3607725).sum := by decide
  have hdescent : baseEnd_3607725 < baseStart_3607725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607741 : List Nat := [1, 4, 1, 2, 1, 1, 2, 2, 3, 3, 3]
def baseStart_3607741 : Nat := 118140960795 + 3607741 * 2 ^ 59
def prefixEnd_3607741 : Nat := 4983230072969 + 3 ^ 40 * 3607741 * 2
def baseEnd_3607741 : Nat := 1852505209932474430445807

theorem tailTrace_3607741 : CollatzResearch.WordTrace tailWord_3607741 prefixEnd_3607741 1852505209932474430445807 := by
  unfold tailWord_3607741
  simp only [CollatzResearch.WordTrace]
  refine ⟨131585124422777984953455077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87723416281851989968970051 131585124422777984953455077)
  ·
    refine ⟨24672210829270872178772827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131585124422777984953455077 24672210829270872178772827)
    ·
      refine ⟨37008316243906308268159241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24672210829270872178772827 37008316243906308268159241)
      ·
        refine ⟨27756237182929731201119431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37008316243906308268159241 27756237182929731201119431)
        ·
          refine ⟨41634355774394596801679147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27756237182929731201119431 41634355774394596801679147)
          ·
            refine ⟨62451533661591895202518721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41634355774394596801679147 62451533661591895202518721)
            ·
              refine ⟨46838650246193921401889041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62451533661591895202518721 46838650246193921401889041)
              ·
                refine ⟨35128987684645441051416781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46838650246193921401889041 35128987684645441051416781)
                ·
                  refine ⟨13173370381742040394281293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35128987684645441051416781 13173370381742040394281293)
                  ·
                    refine ⟨4940013893153265147855485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13173370381742040394281293 4940013893153265147855485)
                    ·
                      refine ⟨1852505209932474430445807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4940013893153265147855485 1852505209932474430445807)
                      ·
                        rfl

theorem cell23_3607741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_3607741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3607741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3607741 prefixEnd_3607741 := by exact prefixLift 3607741
  have htrace : WordTrace (prefixWord ++ tailWord_3607741) baseStart_3607741 baseEnd_3607741 := by
    simpa [prefixWord, tailWord_3607741, baseEnd_3607741] using wordTrace_append hprefix tailTrace_3607741
  have hstable : (prefixWord ++ tailWord_3607741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607741).length < 2 ^ (prefixWord ++ tailWord_3607741).sum := by decide
  have hdescent : baseEnd_3607741 < baseStart_3607741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607742 : List Nat := [4, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2]
def baseStart_3607742 : Nat := 118140960795 + 3607742 * 2 ^ 59
def prefixEnd_3607742 : Nat := 4983230072969 + 3 ^ 40 * 3607742 * 2
def baseEnd_3607742 : Nat := 1852505723413128926533303

theorem tailTrace_3607742 : CollatzResearch.WordTrace tailWord_3607742 prefixEnd_3607742 1852505723413128926533303 := by
  unfold tailWord_3607742
  simp only [CollatzResearch.WordTrace]
  refine ⟨16448145111971795265530185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87723440597182908082827653 16448145111971795265530185)
  ·
    refine ⟨12336108833978846449147639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16448145111971795265530185 12336108833978846449147639)
    ·
      refine ⟨18504163250968269673721459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12336108833978846449147639 18504163250968269673721459)
      ·
        refine ⟨27756244876452404510582189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18504163250968269673721459 27756244876452404510582189)
        ·
          refine ⟨10408591828669651691468321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27756244876452404510582189 10408591828669651691468321)
          ·
            refine ⟨7806443871502238768601241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10408591828669651691468321 7806443871502238768601241)
            ·
              refine ⟨5854832903626679076450931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7806443871502238768601241 5854832903626679076450931)
              ·
                refine ⟨8782249355440018614676397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5854832903626679076450931 8782249355440018614676397)
                ·
                  refine ⟨3293343508290006980503649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8782249355440018614676397 3293343508290006980503649)
                  ·
                    refine ⟨2470007631217505235377737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3293343508290006980503649 2470007631217505235377737)
                    ·
                      refine ⟨1852505723413128926533303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2470007631217505235377737 1852505723413128926533303)
                      ·
                        rfl

theorem cell23_3607742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2].length) (baseStart_3607742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3607742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3607742 prefixEnd_3607742 := by exact prefixLift 3607742
  have htrace : WordTrace (prefixWord ++ tailWord_3607742) baseStart_3607742 baseEnd_3607742 := by
    simpa [prefixWord, tailWord_3607742, baseEnd_3607742] using wordTrace_append hprefix tailTrace_3607742
  have hstable : (prefixWord ++ tailWord_3607742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607742).length < 2 ^ (prefixWord ++ tailWord_3607742).sum := by decide
  have hdescent : baseEnd_3607742 < baseStart_3607742 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607801 : List Nat := [1, 2, 1, 3, 1, 1, 4, 1, 2, 4, 3]
def baseStart_3607801 : Nat := 118140960795 + 3607801 * 2 ^ 59
def prefixEnd_3607801 : Nat := 4983230072969 + 3 ^ 40 * 3607801 * 2
def baseEnd_3607801 : Nat := 1852536018771744195695531

theorem tailTrace_3607801 : CollatzResearch.WordTrace tailWord_3607801 prefixEnd_3607801 1852536018771744195695531 := by
  unfold tailWord_3607801
  simp only [CollatzResearch.WordTrace]
  refine ⟨131587312802560615200639257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87724875201707076800426171 131587312802560615200639257)
  ·
    refine ⟨98690484601920461400479443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131587312802560615200639257 98690484601920461400479443)
    ·
      refine ⟨148035726902880692100719165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98690484601920461400479443 148035726902880692100719165)
      ·
        refine ⟨55513397588580259537769687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148035726902880692100719165 55513397588580259537769687)
        ·
          refine ⟨83270096382870389306654531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55513397588580259537769687 83270096382870389306654531)
          ·
            refine ⟨124905144574305583959981797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83270096382870389306654531 124905144574305583959981797)
            ·
              refine ⟨23419714607682296992496587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124905144574305583959981797 23419714607682296992496587)
              ·
                refine ⟨35129571911523445488744881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23419714607682296992496587 35129571911523445488744881)
                ·
                  refine ⟨26347178933642584116558661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35129571911523445488744881 26347178933642584116558661)
                  ·
                    refine ⟨4940096050057984521854749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26347178933642584116558661 4940096050057984521854749)
                    ·
                      refine ⟨1852536018771744195695531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4940096050057984521854749 1852536018771744195695531)
                      ·
                        rfl

theorem cell23_3607801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 4, 3].length) (baseStart_3607801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3607801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3607801 prefixEnd_3607801 := by exact prefixLift 3607801
  have htrace : WordTrace (prefixWord ++ tailWord_3607801) baseStart_3607801 baseEnd_3607801 := by
    simpa [prefixWord, tailWord_3607801, baseEnd_3607801] using wordTrace_append hprefix tailTrace_3607801
  have hstable : (prefixWord ++ tailWord_3607801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607801).length < 2 ^ (prefixWord ++ tailWord_3607801).sum := by decide
  have hdescent : baseEnd_3607801 < baseStart_3607801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607862 : List Nat := [5, 1, 2, 3, 1, 1, 1, 1, 2, 2, 4]
def baseStart_3607862 : Nat := 118140960795 + 3607862 * 2 ^ 59
def prefixEnd_3607862 : Nat := 4983230072969 + 3 ^ 40 * 3607862 * 2
def baseEnd_3607862 : Nat := 1852567341091668457032751

theorem tailTrace_3607862 : CollatzResearch.WordTrace tailWord_3607862 prefixEnd_3607862 1852567341091668457032751 := by
  unfold tailWord_3607862
  simp only [CollatzResearch.WordTrace]
  refine ⟨8224346103458726413663115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87726358436893081745739893 8224346103458726413663115)
  ·
    refine ⟨12336519155188089620494673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8224346103458726413663115 12336519155188089620494673)
    ·
      refine ⟨9252389366391067215371005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12336519155188089620494673 9252389366391067215371005)
      ·
        refine ⟨3469646012396650205764127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9252389366391067215371005 3469646012396650205764127)
        ·
          refine ⟨5204469018594975308646191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3469646012396650205764127 5204469018594975308646191)
          ·
            refine ⟨7806703527892462962969287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5204469018594975308646191 7806703527892462962969287)
            ·
              refine ⟨11710055291838694444453931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7806703527892462962969287 11710055291838694444453931)
              ·
                refine ⟨17565082937758041666680897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11710055291838694444453931 17565082937758041666680897)
                ·
                  refine ⟨13173812203318531250010673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17565082937758041666680897 13173812203318531250010673)
                  ·
                    refine ⟨9880359152488898437508005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13173812203318531250010673 9880359152488898437508005)
                    ·
                      refine ⟨1852567341091668457032751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9880359152488898437508005 1852567341091668457032751)
                      ·
                        rfl

theorem cell23_3607862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_3607862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3607862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3607862 prefixEnd_3607862 := by exact prefixLift 3607862
  have htrace : WordTrace (prefixWord ++ tailWord_3607862) baseStart_3607862 baseEnd_3607862 := by
    simpa [prefixWord, tailWord_3607862, baseEnd_3607862] using wordTrace_append hprefix tailTrace_3607862
  have hstable : (prefixWord ++ tailWord_3607862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607862).length < 2 ^ (prefixWord ++ tailWord_3607862).sum := by decide
  have hdescent : baseEnd_3607862 < baseStart_3607862 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607865 : List Nat := [1, 2, 1, 6, 2, 1, 1, 1, 2, 3, 3]
def baseStart_3607865 : Nat := 118140960795 + 3607865 * 2 ^ 59
def prefixEnd_3607865 : Nat := 4983230072969 + 3 ^ 40 * 3607865 * 2
def baseEnd_3607865 : Nat := 1852568881533631945295237

theorem tailTrace_3607865 : CollatzResearch.WordTrace tailWord_3607865 prefixEnd_3607865 1852568881533631945295237 := by
  unfold tailWord_3607865
  simp only [CollatzResearch.WordTrace]
  refine ⟨131589647074328754130969049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87726431382885836087312699 131589647074328754130969049)
  ·
    refine ⟨98692235305746565598226787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131589647074328754130969049 98692235305746565598226787)
    ·
      refine ⟨148038352958619848397340181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98692235305746565598226787 148038352958619848397340181)
      ·
        refine ⟨6939297794935305393625321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 148038352958619848397340181 6939297794935305393625321)
        ·
          refine ⟨5204473346201479045218991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6939297794935305393625321 5204473346201479045218991)
          ·
            refine ⟨7806710019302218567828487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5204473346201479045218991 7806710019302218567828487)
            ·
              refine ⟨11710065028953327851742731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7806710019302218567828487 11710065028953327851742731)
              ·
                refine ⟨17565097543429991777614097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11710065028953327851742731 17565097543429991777614097)
                ·
                  refine ⟨13173823157572493833210573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17565097543429991777614097 13173823157572493833210573)
                  ·
                    refine ⟨4940183684089685187453965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13173823157572493833210573 4940183684089685187453965)
                    ·
                      refine ⟨1852568881533631945295237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4940183684089685187453965 1852568881533631945295237)
                      ·
                        rfl

theorem cell23_3607865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_3607865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3607865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3607865 prefixEnd_3607865 := by exact prefixLift 3607865
  have htrace : WordTrace (prefixWord ++ tailWord_3607865) baseStart_3607865 baseEnd_3607865 := by
    simpa [prefixWord, tailWord_3607865, baseEnd_3607865] using wordTrace_append hprefix tailTrace_3607865
  have hstable : (prefixWord ++ tailWord_3607865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607865).length < 2 ^ (prefixWord ++ tailWord_3607865).sum := by decide
  have hdescent : baseEnd_3607865 < baseStart_3607865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607888 : List Nat := [2, 1, 1, 1, 1, 5, 1, 2, 1, 6, 2]
def baseStart_3607888 : Nat := 118140960795 + 3607888 * 2 ^ 59
def prefixEnd_3607888 : Nat := 4983230072969 + 3 ^ 40 * 3607888 * 2
def baseEnd_3607888 : Nat := 1852580691588685355307631

theorem tailTrace_3607888 : CollatzResearch.WordTrace tailWord_3607888 prefixEnd_3607888 1852580691588685355307631 := by
  unfold tailWord_3607888
  simp only [CollatzResearch.WordTrace]
  refine ⟨65795242976622714529528159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87726990635496952706037545 65795242976622714529528159)
  ·
    refine ⟨98692864464934071794292239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65795242976622714529528159 98692864464934071794292239)
    ·
      refine ⟨148039296697401107691438359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98692864464934071794292239 148039296697401107691438359)
      ·
        refine ⟨222058945046101661537157539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148039296697401107691438359 222058945046101661537157539)
        ·
          refine ⟨333088417569152492305736309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222058945046101661537157539 333088417569152492305736309)
          ·
            refine ⟨31227039147108046153662779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 333088417569152492305736309 31227039147108046153662779)
            ·
              refine ⟨46840558720662069230494169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31227039147108046153662779 46840558720662069230494169)
              ·
                refine ⟨35130419040496551922870627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46840558720662069230494169 35130419040496551922870627)
                ·
                  refine ⟨52695628560744827884305941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35130419040496551922870627 52695628560744827884305941)
                  ·
                    refine ⟨2470107588784913807076841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 52695628560744827884305941 2470107588784913807076841)
                    ·
                      refine ⟨1852580691588685355307631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2470107588784913807076841 1852580691588685355307631)
                      ·
                        rfl

theorem cell23_3607888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 1, 6, 2].length) (baseStart_3607888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3607888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3607888 prefixEnd_3607888 := by exact prefixLift 3607888
  have htrace : WordTrace (prefixWord ++ tailWord_3607888) baseStart_3607888 baseEnd_3607888 := by
    simpa [prefixWord, tailWord_3607888, baseEnd_3607888] using wordTrace_append hprefix tailTrace_3607888
  have hstable : (prefixWord ++ tailWord_3607888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607888).length < 2 ^ (prefixWord ++ tailWord_3607888).sum := by decide
  have hdescent : baseEnd_3607888 < baseStart_3607888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607931 : List Nat := [1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 6]
def baseStart_3607931 : Nat := 118140960795 + 3607931 * 2 ^ 59
def prefixEnd_3607931 : Nat := 4983230072969 + 3 ^ 40 * 3607931 * 2
def baseEnd_3607931 : Nat := 1852602771256828687069933

theorem tailTrace_3607931 : CollatzResearch.WordTrace tailWord_3607931 prefixEnd_3607931 1852602771256828687069933 := by
  unfold tailWord_3607931
  simp only [CollatzResearch.WordTrace]
  refine ⟨131592054292089647402871647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87728036194726431601914431 131592054292089647402871647)
  ·
    refine ⟨197388081438134471104307471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131592054292089647402871647 197388081438134471104307471)
    ·
      refine ⟨296082122157201706656461207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197388081438134471104307471 296082122157201706656461207)
      ·
        refine ⟨444123183235802559984691811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296082122157201706656461207 444123183235802559984691811)
        ·
          refine ⟨666184774853703839977037717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444123183235802559984691811 666184774853703839977037717)
          ·
            refine ⟨31227411321267367498923643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 666184774853703839977037717 31227411321267367498923643)
            ·
              refine ⟨46841116981901051248385465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31227411321267367498923643 46841116981901051248385465)
              ·
                refine ⟨35130837736425788436289099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46841116981901051248385465 35130837736425788436289099)
                ·
                  refine ⟨52696256604638682654433649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35130837736425788436289099 52696256604638682654433649)
                  ·
                    refine ⟨39522192453479011990825237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52696256604638682654433649 39522192453479011990825237)
                    ·
                      refine ⟨1852602771256828687069933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39522192453479011990825237 1852602771256828687069933)
                      ·
                        rfl

theorem cell23_3607931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 6].length) (baseStart_3607931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3607931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3607931 prefixEnd_3607931 := by exact prefixLift 3607931
  have htrace : WordTrace (prefixWord ++ tailWord_3607931) baseStart_3607931 baseEnd_3607931 := by
    simpa [prefixWord, tailWord_3607931, baseEnd_3607931] using wordTrace_append hprefix tailTrace_3607931
  have hstable : (prefixWord ++ tailWord_3607931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607931).length < 2 ^ (prefixWord ++ tailWord_3607931).sum := by decide
  have hdescent : baseEnd_3607931 < baseStart_3607931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3607966 : List Nat := [4, 3, 1, 2, 3, 1, 1, 1, 3, 4]
def baseStart_3607966 : Nat := 118140960795 + 3607966 * 2 ^ 59
def prefixEnd_3607966 : Nat := 4983230072969 + 3 ^ 40 * 3607966 * 2
def baseEnd_3607966 : Nat := 617540247693245350044091

theorem tailTrace_3607966 : CollatzResearch.WordTrace tailWord_3607966 prefixEnd_3607966 617540247693245350044091 := by
  unfold tailWord_3607966
  simp only [CollatzResearch.WordTrace]
  refine ⟨16449166355870356047549469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87728887231308565586930501 16449166355870356047549469)
  ·
    refine ⟨6168437383451383517831051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16449166355870356047549469 6168437383451383517831051)
    ·
      refine ⟨9252656075177075276746577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6168437383451383517831051 9252656075177075276746577)
      ·
        refine ⟨6939492056382806457559933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9252656075177075276746577 6939492056382806457559933)
        ·
          refine ⟨2602309521143552421584975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6939492056382806457559933 2602309521143552421584975)
          ·
            refine ⟨3903464281715328632377463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2602309521143552421584975 3903464281715328632377463)
            ·
              refine ⟨5855196422572992948566195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3903464281715328632377463 5855196422572992948566195)
              ·
                refine ⟨8782794633859489422849293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5855196422572992948566195 8782794633859489422849293)
                ·
                  refine ⟨3293547987697308533568485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8782794633859489422849293 3293547987697308533568485)
                  ·
                    refine ⟨617540247693245350044091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3293547987697308533568485 617540247693245350044091)
                    ·
                      rfl

theorem cell23_3607966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_3607966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3607966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3607966 prefixEnd_3607966 := by exact prefixLift 3607966
  have htrace : WordTrace (prefixWord ++ tailWord_3607966) baseStart_3607966 baseEnd_3607966 := by
    simpa [prefixWord, tailWord_3607966, baseEnd_3607966] using wordTrace_append hprefix tailTrace_3607966
  have hstable : (prefixWord ++ tailWord_3607966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3607966).length < 2 ^ (prefixWord ++ tailWord_3607966).sum := by decide
  have hdescent : baseEnd_3607966 < baseStart_3607966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3607966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608015 : List Nat := [1, 1, 2, 1, 1, 4, 2, 5, 1, 2, 3]
def baseStart_3608015 : Nat := 118140960795 + 3608015 * 2 ^ 59
def prefixEnd_3608015 : Nat := 4983230072969 + 3 ^ 40 * 3608015 * 2
def baseEnd_3608015 : Nat := 1852645903631806358419547

theorem tailTrace_3608015 : CollatzResearch.WordTrace tailWord_3608015 prefixEnd_3608015 1852645903631806358419547 := by
  unfold tailWord_3608015
  simp only [CollatzResearch.WordTrace]
  refine ⟨131595118023785329748929499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87730078682523553165952999 131595118023785329748929499)
  ·
    refine ⟨197392677035677994623394249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131595118023785329748929499 197392677035677994623394249)
    ·
      refine ⟨148044507776758495967545687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197392677035677994623394249 148044507776758495967545687)
      ·
        refine ⟨222066761665137743951318531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148044507776758495967545687 222066761665137743951318531)
        ·
          refine ⟨333100142497706615926977797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222066761665137743951318531 333100142497706615926977797)
          ·
            refine ⟨62456276718319990486308337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 333100142497706615926977797 62456276718319990486308337)
            ·
              refine ⟨46842207538739992864731253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62456276718319990486308337 46842207538739992864731253)
              ·
                refine ⟨4391456956756874331068555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46842207538739992864731253 4391456956756874331068555)
                ·
                  refine ⟨6587185435135311496602833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4391456956756874331068555 6587185435135311496602833)
                  ·
                    refine ⟨4940389076351483622452125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6587185435135311496602833 4940389076351483622452125)
                    ·
                      refine ⟨1852645903631806358419547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4940389076351483622452125 1852645903631806358419547)
                      ·
                        rfl

theorem cell23_3608015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 5, 1, 2, 3].length) (baseStart_3608015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3608015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3608015 prefixEnd_3608015 := by exact prefixLift 3608015
  have htrace : WordTrace (prefixWord ++ tailWord_3608015) baseStart_3608015 baseEnd_3608015 := by
    simpa [prefixWord, tailWord_3608015, baseEnd_3608015] using wordTrace_append hprefix tailTrace_3608015
  have hstable : (prefixWord ++ tailWord_3608015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608015).length < 2 ^ (prefixWord ++ tailWord_3608015).sum := by decide
  have hdescent : baseEnd_3608015 < baseStart_3608015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608035 : List Nat := [1, 1, 1, 6, 2, 3, 1, 8]
def baseStart_3608035 : Nat := 118140960795 + 3608035 * 2 ^ 59
def prefixEnd_3608035 : Nat := 4983230072969 + 3 ^ 40 * 3608035 * 2
def baseEnd_3608035 : Nat := 68616895305366528895165

theorem tailTrace_3608035 : CollatzResearch.WordTrace tailWord_3608035 prefixEnd_3608035 68616895305366528895165 := by
  unfold tailWord_3608035
  simp only [CollatzResearch.WordTrace]
  refine ⟨131595847483712873164657559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87730564989141915443105039 131595847483712873164657559)
  ·
    refine ⟨197393771225569309746986339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131595847483712873164657559 197393771225569309746986339)
    ·
      refine ⟨296090656838353964620479509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197393771225569309746986339 296090656838353964620479509)
      ·
        refine ⟨13879249539297842091584977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 296090656838353964620479509 13879249539297842091584977)
        ·
          refine ⟨10409437154473381568688733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13879249539297842091584977 10409437154473381568688733)
          ·
            refine ⟨3903538932927518088258275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10409437154473381568688733 3903538932927518088258275)
            ·
              refine ⟨5855308399391277132387413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3903538932927518088258275 5855308399391277132387413)
              ·
                refine ⟨68616895305366528895165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5855308399391277132387413 68616895305366528895165)
                ·
                  rfl

theorem cell23_3608035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 8].length) (baseStart_3608035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3608035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3608035 prefixEnd_3608035 := by exact prefixLift 3608035
  have htrace : WordTrace (prefixWord ++ tailWord_3608035) baseStart_3608035 baseEnd_3608035 := by
    simpa [prefixWord, tailWord_3608035, baseEnd_3608035] using wordTrace_append hprefix tailTrace_3608035
  have hstable : (prefixWord ++ tailWord_3608035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608035).length < 2 ^ (prefixWord ++ tailWord_3608035).sum := by decide
  have hdescent : baseEnd_3608035 < baseStart_3608035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608042 : List Nat := [3, 1, 3, 1, 4, 1, 2, 1, 1, 2, 4]
def baseStart_3608042 : Nat := 118140960795 + 3608042 * 2 ^ 59
def prefixEnd_3608042 : Nat := 4983230072969 + 3 ^ 40 * 3608042 * 2
def baseEnd_3608042 : Nat := 1852659767609477752781923

theorem tailTrace_3608042 : CollatzResearch.WordTrace tailWord_3608042 prefixEnd_3608042 1852659767609477752781923 := by
  unfold tailWord_3608042
  simp only [CollatzResearch.WordTrace]
  refine ⟨32899025698671878340040595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87730735196458342240108253 32899025698671878340040595)
  ·
    refine ⟨49348538548007817510060893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32899025698671878340040595 49348538548007817510060893)
    ·
      refine ⟨18505701955502931566272835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49348538548007817510060893 18505701955502931566272835)
      ·
        refine ⟨27758552933254397349409253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18505701955502931566272835 27758552933254397349409253)
        ·
          refine ⟨5204728674985199503014235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27758552933254397349409253 5204728674985199503014235)
          ·
            refine ⟨7807093012477799254521353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5204728674985199503014235 7807093012477799254521353)
            ·
              refine ⟨5855319759358349440891015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7807093012477799254521353 5855319759358349440891015)
              ·
                refine ⟨8782979639037524161336523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5855319759358349440891015 8782979639037524161336523)
                ·
                  refine ⟨13174469458556286242004785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8782979639037524161336523 13174469458556286242004785)
                  ·
                    refine ⟨9880852093917214681503589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13174469458556286242004785 9880852093917214681503589)
                    ·
                      refine ⟨1852659767609477752781923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9880852093917214681503589 1852659767609477752781923)
                      ·
                        rfl

theorem cell23_3608042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_3608042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3608042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3608042 prefixEnd_3608042 := by exact prefixLift 3608042
  have htrace : WordTrace (prefixWord ++ tailWord_3608042) baseStart_3608042 baseEnd_3608042 := by
    simpa [prefixWord, tailWord_3608042, baseEnd_3608042] using wordTrace_append hprefix tailTrace_3608042
  have hstable : (prefixWord ++ tailWord_3608042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608042).length < 2 ^ (prefixWord ++ tailWord_3608042).sum := by decide
  have hdescent : baseEnd_3608042 < baseStart_3608042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608058 : List Nat := [3, 1, 1, 1, 1, 2, 4, 1, 2, 2, 5]
def baseStart_3608058 : Nat := 118140960795 + 3608058 * 2 ^ 59
def prefixEnd_3608058 : Nat := 4983230072969 + 3 ^ 40 * 3608058 * 2
def baseEnd_3608058 : Nat := 1852667983299949690181849

theorem tailTrace_3608058 : CollatzResearch.WordTrace tailWord_3608058 prefixEnd_3608058 1852667983299949690181849 := by
  unfold tailWord_3608058
  simp only [CollatzResearch.WordTrace]
  refine ⟨32899171590657387023186207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87731124241753032061829885 32899171590657387023186207)
  ·
    refine ⟨49348757385986080534779311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32899171590657387023186207 49348757385986080534779311)
    ·
      refine ⟨74023136078979120802168967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49348757385986080534779311 74023136078979120802168967)
      ·
        refine ⟨111034704118468681203253451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74023136078979120802168967 111034704118468681203253451)
        ·
          refine ⟨166552056177703021804880177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111034704118468681203253451 166552056177703021804880177)
          ·
            refine ⟨124914042133277266353660133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166552056177703021804880177 124914042133277266353660133)
            ·
              refine ⟨23421382899989487441311275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124914042133277266353660133 23421382899989487441311275)
              ·
                refine ⟨35132074349984231161966913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23421382899989487441311275 35132074349984231161966913)
                ·
                  refine ⟨26349055762488173371475185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35132074349984231161966913 26349055762488173371475185)
                  ·
                    refine ⟨19761791821866130028606389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26349055762488173371475185 19761791821866130028606389)
                    ·
                      refine ⟨1852667983299949690181849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19761791821866130028606389 1852667983299949690181849)
                      ·
                        rfl

theorem cell23_3608058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 2, 2, 5].length) (baseStart_3608058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3608058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3608058 prefixEnd_3608058 := by exact prefixLift 3608058
  have htrace : WordTrace (prefixWord ++ tailWord_3608058) baseStart_3608058 baseEnd_3608058 := by
    simpa [prefixWord, tailWord_3608058, baseEnd_3608058] using wordTrace_append hprefix tailTrace_3608058
  have hstable : (prefixWord ++ tailWord_3608058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608058).length < 2 ^ (prefixWord ++ tailWord_3608058).sum := by decide
  have hdescent : baseEnd_3608058 < baseStart_3608058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608066 : List Nat := [3, 4, 1, 2, 1, 1, 4, 1, 1, 2, 3]
def baseStart_3608066 : Nat := 118140960795 + 3608066 * 2 ^ 59
def prefixEnd_3608066 : Nat := 4983230072969 + 3 ^ 40 * 3608066 * 2
def baseEnd_3608066 : Nat := 1852672091145185658881813

theorem tailTrace_3608066 : CollatzResearch.WordTrace tailWord_3608066 prefixEnd_3608066 1852672091145185658881813 := by
  unfold tailWord_3608066
  simp only [CollatzResearch.WordTrace]
  refine ⟨32899244536650141364759013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87731318764400376972690701 32899244536650141364759013)
  ·
    refine ⟨6168608350621901505892315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32899244536650141364759013 6168608350621901505892315)
    ·
      refine ⟨9252912525932852258838473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6168608350621901505892315 9252912525932852258838473)
      ·
        refine ⟨6939684394449639194128855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9252912525932852258838473 6939684394449639194128855)
        ·
          refine ⟨10409526591674458791193283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6939684394449639194128855 10409526591674458791193283)
          ·
            refine ⟨15614289887511688186789925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10409526591674458791193283 15614289887511688186789925)
            ·
              refine ⟨2927679353908441535023111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15614289887511688186789925 2927679353908441535023111)
              ·
                refine ⟨4391519030862662302534667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2927679353908441535023111 4391519030862662302534667)
                ·
                  refine ⟨6587278546293993453802001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4391519030862662302534667 6587278546293993453802001)
                  ·
                    refine ⟨4940458909720495090351501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6587278546293993453802001 4940458909720495090351501)
                    ·
                      refine ⟨1852672091145185658881813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4940458909720495090351501 1852672091145185658881813)
                      ·
                        rfl

theorem cell23_3608066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_3608066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3608066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3608066 prefixEnd_3608066 := by exact prefixLift 3608066
  have htrace : WordTrace (prefixWord ++ tailWord_3608066) baseStart_3608066 baseEnd_3608066 := by
    simpa [prefixWord, tailWord_3608066, baseEnd_3608066] using wordTrace_append hprefix tailTrace_3608066
  have hstable : (prefixWord ++ tailWord_3608066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608066).length < 2 ^ (prefixWord ++ tailWord_3608066).sum := by decide
  have hdescent : baseEnd_3608066 < baseStart_3608066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608096 : List Nat := [2, 1, 1, 6, 1, 2, 3, 1, 2, 1, 3]
def baseStart_3608096 : Nat := 118140960795 + 3608096 * 2 ^ 59
def prefixEnd_3608096 : Nat := 4983230072969 + 3 ^ 40 * 3608096 * 2
def baseEnd_3608096 : Nat := 1852687495564820541506675

theorem tailTrace_3608096 : CollatzResearch.WordTrace tailWord_3608096 prefixEnd_3608096 1852687495564820541506675 := by
  unfold tailWord_3608096
  simp only [CollatzResearch.WordTrace]
  refine ⟨65799036168245940291314071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87732048224327920388418761 65799036168245940291314071)
  ·
    refine ⟨98698554252368910436971107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65799036168245940291314071 98698554252368910436971107)
    ·
      refine ⟨148047831378553365655456661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98698554252368910436971107 148047831378553365655456661)
      ·
        refine ⟨6939742095869689015099531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 148047831378553365655456661 6939742095869689015099531)
        ·
          refine ⟨10409613143804533522649297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6939742095869689015099531 10409613143804533522649297)
          ·
            refine ⟨7807209857853400141986973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10409613143804533522649297 7807209857853400141986973)
            ·
              refine ⟨2927703696695025053245115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7807209857853400141986973 2927703696695025053245115)
              ·
                refine ⟨4391555545042537579867673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2927703696695025053245115 4391555545042537579867673)
                ·
                  refine ⟨3293666658781903184900755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4391555545042537579867673 3293666658781903184900755)
                  ·
                    refine ⟨4940499988172854777351133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3293666658781903184900755 4940499988172854777351133)
                    ·
                      refine ⟨1852687495564820541506675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4940499988172854777351133 1852687495564820541506675)
                      ·
                        rfl

theorem cell23_3608096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_3608096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3608096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3608096 prefixEnd_3608096 := by exact prefixLift 3608096
  have htrace : WordTrace (prefixWord ++ tailWord_3608096) baseStart_3608096 baseEnd_3608096 := by
    simpa [prefixWord, tailWord_3608096, baseEnd_3608096] using wordTrace_append hprefix tailTrace_3608096
  have hstable : (prefixWord ++ tailWord_3608096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608096).length < 2 ^ (prefixWord ++ tailWord_3608096).sum := by decide
  have hdescent : baseEnd_3608096 < baseStart_3608096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608182 : List Nat := [5, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5]
def baseStart_3608182 : Nat := 118140960795 + 3608182 * 2 ^ 59
def prefixEnd_3608182 : Nat := 4983230072969 + 3 ^ 40 * 3608182 * 2
def baseEnd_3608182 : Nat := 1852731654901107205031279

theorem tailTrace_3608182 : CollatzResearch.WordTrace tailWord_3608182 prefixEnd_3608182 1852731654901107205031279 := by
  unfold tailWord_3608182
  simp only [CollatzResearch.WordTrace]
  refine ⟨8225075563386269829391175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87734139342786878180172533 8225075563386269829391175)
  ·
    refine ⟨12337613345079404744086763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8225075563386269829391175 12337613345079404744086763)
    ·
      refine ⟨18506420017619107116130145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12337613345079404744086763 18506420017619107116130145)
      ·
        refine ⟨13879815013214330337097609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18506420017619107116130145 13879815013214330337097609)
        ·
          refine ⟨10409861259910747752823207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13879815013214330337097609 10409861259910747752823207)
          ·
            refine ⟨15614791889866121629234811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10409861259910747752823207 15614791889866121629234811)
            ·
              refine ⟨23422187834799182443852217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15614791889866121629234811 23422187834799182443852217)
              ·
                refine ⟨17566640876099386832889163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23422187834799182443852217 17566640876099386832889163)
                ·
                  refine ⟨26349961314149080249333745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17566640876099386832889163 26349961314149080249333745)
                  ·
                    refine ⟨19762470985611810187000309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26349961314149080249333745 19762470985611810187000309)
                    ·
                      refine ⟨1852731654901107205031279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19762470985611810187000309 1852731654901107205031279)
                      ·
                        rfl

theorem cell23_3608182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_3608182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3608182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3608182 prefixEnd_3608182 := by exact prefixLift 3608182
  have htrace : WordTrace (prefixWord ++ tailWord_3608182) baseStart_3608182 baseEnd_3608182 := by
    simpa [prefixWord, tailWord_3608182, baseEnd_3608182] using wordTrace_append hprefix tailTrace_3608182
  have hstable : (prefixWord ++ tailWord_3608182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608182).length < 2 ^ (prefixWord ++ tailWord_3608182).sum := by decide
  have hdescent : baseEnd_3608182 < baseStart_3608182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608192 : List Nat := [2, 1, 1, 2, 1, 4, 2, 2, 2, 4, 2]
def baseStart_3608192 : Nat := 118140960795 + 3608192 * 2 ^ 59
def prefixEnd_3608192 : Nat := 4983230072969 + 3 ^ 40 * 3608192 * 2
def baseEnd_3608192 : Nat := 1852736789707652165906233

theorem tailTrace_3608192 : CollatzResearch.WordTrace tailWord_3608192 prefixEnd_3608192 1852736789707652165906233 := by
  unfold tailWord_3608192
  simp only [CollatzResearch.WordTrace]
  refine ⟨65800786872072044489061415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87734382496096059318748553 65800786872072044489061415)
  ·
    refine ⟨98701180308108066733592123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65800786872072044489061415 98701180308108066733592123)
    ·
      refine ⟨148051770462162100100388185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98701180308108066733592123 148051770462162100100388185)
      ·
        refine ⟨111038827846621575075291139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148051770462162100100388185 111038827846621575075291139)
        ·
          refine ⟨166558241769932362612936709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111038827846621575075291139 166558241769932362612936709)
          ·
            refine ⟨31229670331862317989925633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 166558241769932362612936709 31229670331862317989925633)
            ·
              refine ⟨23422252748896738492444225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31229670331862317989925633 23422252748896738492444225)
              ·
                refine ⟨17566689561672553869333169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23422252748896738492444225 17566689561672553869333169)
                ·
                  refine ⟨13175017171254415401999877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17566689561672553869333169 13175017171254415401999877)
                  ·
                    refine ⟨2470315719610202887874977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13175017171254415401999877 2470315719610202887874977)
                    ·
                      refine ⟨1852736789707652165906233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2470315719610202887874977 1852736789707652165906233)
                      ·
                        rfl

theorem cell23_3608192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 2, 4, 2].length) (baseStart_3608192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3608192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3608192 prefixEnd_3608192 := by exact prefixLift 3608192
  have htrace : WordTrace (prefixWord ++ tailWord_3608192) baseStart_3608192 baseEnd_3608192 := by
    simpa [prefixWord, tailWord_3608192, baseEnd_3608192] using wordTrace_append hprefix tailTrace_3608192
  have hstable : (prefixWord ++ tailWord_3608192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608192).length < 2 ^ (prefixWord ++ tailWord_3608192).sum := by decide
  have hdescent : baseEnd_3608192 < baseStart_3608192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608195 : List Nat := [1, 1, 1, 3, 3, 1, 1, 2, 3, 4, 3]
def baseStart_3608195 : Nat := 118140960795 + 3608195 * 2 ^ 59
def prefixEnd_3608195 : Nat := 4983230072969 + 3 ^ 40 * 3608195 * 2
def baseEnd_3608195 : Nat := 1852738330149615654168719

theorem tailTrace_3608195 : CollatzResearch.WordTrace tailWord_3608195 prefixEnd_3608195 1852738330149615654168719 := by
  unfold tailWord_3608195
  simp only [CollatzResearch.WordTrace]
  refine ⟨131601683163133220490482039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87734455442088813660321359 131601683163133220490482039)
  ·
    refine ⟨197402524744699830735723059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131601683163133220490482039 197402524744699830735723059)
    ·
      refine ⟨296103787117049746103584589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197402524744699830735723059 296103787117049746103584589)
      ·
        refine ⟨111038920168893654788844221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 296103787117049746103584589 111038920168893654788844221)
        ·
          refine ⟨41639595063335120545816583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111038920168893654788844221 41639595063335120545816583)
          ·
            refine ⟨62459392595002680818724875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41639595063335120545816583 62459392595002680818724875)
            ·
              refine ⟨93689088892504021228087313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62459392595002680818724875 93689088892504021228087313)
              ·
                refine ⟨70266816669378015921065485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93689088892504021228087313 70266816669378015921065485)
                ·
                  refine ⟨26350056251016755970399557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70266816669378015921065485 26350056251016755970399557)
                  ·
                    refine ⟨4940635547065641744449917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26350056251016755970399557 4940635547065641744449917)
                    ·
                      refine ⟨1852738330149615654168719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4940635547065641744449917 1852738330149615654168719)
                      ·
                        rfl

theorem cell23_3608195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 4, 3].length) (baseStart_3608195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3608195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3608195 prefixEnd_3608195 := by exact prefixLift 3608195
  have htrace : WordTrace (prefixWord ++ tailWord_3608195) baseStart_3608195 baseEnd_3608195 := by
    simpa [prefixWord, tailWord_3608195, baseEnd_3608195] using wordTrace_append hprefix tailTrace_3608195
  have hstable : (prefixWord ++ tailWord_3608195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608195).length < 2 ^ (prefixWord ++ tailWord_3608195).sum := by decide
  have hdescent : baseEnd_3608195 < baseStart_3608195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608276 : List Nat := [2, 4, 1, 3, 1, 1, 2, 2, 3, 1, 3]
def baseStart_3608276 : Nat := 118140960795 + 3608276 * 2 ^ 59
def prefixEnd_3608276 : Nat := 4983230072969 + 3 ^ 40 * 3608276 * 2
def baseEnd_3608276 : Nat := 1852779922082629837255847

theorem tailTrace_3608276 : CollatzResearch.WordTrace tailWord_3608276 prefixEnd_3608276 1852779922082629837255847 := by
  unfold tailWord_3608276
  simp only [CollatzResearch.WordTrace]
  refine ⟨65802318737919885662090341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87736424983893180882787121 65802318737919885662090341)
  ·
    refine ⟨12337934763359978561641939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65802318737919885662090341 12337934763359978561641939)
    ·
      refine ⟨18506902145039967842462909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12337934763359978561641939 18506902145039967842462909)
      ·
        refine ⟨6940088304389987940923591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18506902145039967842462909 6940088304389987940923591)
        ·
          refine ⟨10410132456584981911385387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6940088304389987940923591 10410132456584981911385387)
          ·
            refine ⟨15615198684877472867078081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10410132456584981911385387 15615198684877472867078081)
            ·
              refine ⟨11711399013658104650308561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15615198684877472867078081 11711399013658104650308561)
              ·
                refine ⟨8783549260243578487731421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11711399013658104650308561 8783549260243578487731421)
                ·
                  refine ⟨3293830972591341932899283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8783549260243578487731421 3293830972591341932899283)
                  ·
                    refine ⟨4940746458887012899348925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3293830972591341932899283 4940746458887012899348925)
                    ·
                      refine ⟨1852779922082629837255847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4940746458887012899348925 1852779922082629837255847)
                      ·
                        rfl

theorem cell23_3608276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_3608276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3608276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3608276 prefixEnd_3608276 := by exact prefixLift 3608276
  have htrace : WordTrace (prefixWord ++ tailWord_3608276) baseStart_3608276 baseEnd_3608276 := by
    simpa [prefixWord, tailWord_3608276, baseEnd_3608276] using wordTrace_append hprefix tailTrace_3608276
  have hstable : (prefixWord ++ tailWord_3608276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608276).length < 2 ^ (prefixWord ++ tailWord_3608276).sum := by decide
  have hdescent : baseEnd_3608276 < baseStart_3608276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608292 : List Nat := [2, 3, 1, 1, 1, 3, 1, 1, 6, 4]
def baseStart_3608292 : Nat := 118140960795 + 3608292 * 2 ^ 59
def prefixEnd_3608292 : Nat := 4983230072969 + 3 ^ 40 * 3608292 * 2
def baseEnd_3608292 : Nat := 617596045924367258218591

theorem tailTrace_3608292 : CollatzResearch.WordTrace tailWord_3608292 prefixEnd_3608292 617596045924367258218591 := by
  unfold tailWord_3608292
  simp only [CollatzResearch.WordTrace]
  refine ⟨65802610521890903028381565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87736814029187870704508753 65802610521890903028381565)
  ·
    refine ⟨24675978945709088635643087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65802610521890903028381565 24675978945709088635643087)
    ·
      refine ⟨37013968418563632953464631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24675978945709088635643087 37013968418563632953464631)
      ·
        refine ⟨55520952627845449430196947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37013968418563632953464631 55520952627845449430196947)
        ·
          refine ⟨83281428941768174145295421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55520952627845449430196947 83281428941768174145295421)
          ·
            refine ⟨31230535853163065304485783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83281428941768174145295421 31230535853163065304485783)
            ·
              refine ⟨46845803779744597956728675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31230535853163065304485783 46845803779744597956728675)
              ·
                refine ⟨70268705669616896935093013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46845803779744597956728675 70268705669616896935093013)
                ·
                  refine ⟨3293845578263292043832485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 70268705669616896935093013 3293845578263292043832485)
                  ·
                    refine ⟨617596045924367258218591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3293845578263292043832485 617596045924367258218591)
                    ·
                      rfl

theorem cell23_3608292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 6, 4].length) (baseStart_3608292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3608292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3608292 prefixEnd_3608292 := by exact prefixLift 3608292
  have htrace : WordTrace (prefixWord ++ tailWord_3608292) baseStart_3608292 baseEnd_3608292 := by
    simpa [prefixWord, tailWord_3608292, baseEnd_3608292] using wordTrace_append hprefix tailTrace_3608292
  have hstable : (prefixWord ++ tailWord_3608292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608292).length < 2 ^ (prefixWord ++ tailWord_3608292).sum := by decide
  have hdescent : baseEnd_3608292 < baseStart_3608292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608299 : List Nat := [1, 1, 1, 1, 2, 4, 2, 2, 5, 2, 2]
def baseStart_3608299 : Nat := 118140960795 + 3608299 * 2 ^ 59
def prefixEnd_3608299 : Nat := 4983230072969 + 3 ^ 40 * 3608299 * 2
def baseEnd_3608299 : Nat := 1852791732137683247268241

theorem tailTrace_3608299 : CollatzResearch.WordTrace tailWord_3608299 prefixEnd_3608299 1852791732137683247268241 := by
  unfold tailWord_3608299
  simp only [CollatzResearch.WordTrace]
  refine ⟨131605476354756446252267951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87736984236504297501511967 131605476354756446252267951)
  ·
    refine ⟨197408214532134669378401927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131605476354756446252267951 197408214532134669378401927)
    ·
      refine ⟨296112321798202004067602891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197408214532134669378401927 296112321798202004067602891)
      ·
        refine ⟨444168482697303006101404337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296112321798202004067602891 444168482697303006101404337)
        ·
          refine ⟨333126362022977254576053253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 444168482697303006101404337 333126362022977254576053253)
          ·
            refine ⟨62461192879308235233009985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 333126362022977254576053253 62461192879308235233009985)
            ·
              refine ⟨46845894659481176424757489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62461192879308235233009985 46845894659481176424757489)
              ·
                refine ⟨35134420994610882318568117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46845894659481176424757489 35134420994610882318568117)
                ·
                  refine ⟨3293851968244770217365761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35134420994610882318568117 3293851968244770217365761)
                  ·
                    refine ⟨2470388976183577663024321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3293851968244770217365761 2470388976183577663024321)
                    ·
                      refine ⟨1852791732137683247268241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2470388976183577663024321 1852791732137683247268241)
                      ·
                        rfl

theorem cell23_3608299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 5, 2, 2].length) (baseStart_3608299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3608299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3608299 prefixEnd_3608299 := by exact prefixLift 3608299
  have htrace : WordTrace (prefixWord ++ tailWord_3608299) baseStart_3608299 baseEnd_3608299 := by
    simpa [prefixWord, tailWord_3608299, baseEnd_3608299] using wordTrace_append hprefix tailTrace_3608299
  have hstable : (prefixWord ++ tailWord_3608299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608299).length < 2 ^ (prefixWord ++ tailWord_3608299).sum := by decide
  have hdescent : baseEnd_3608299 < baseStart_3608299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608305 : List Nat := [1, 2, 2, 2, 2, 3, 11]
def baseStart_3608305 : Nat := 118140960795 + 3608305 * 2 ^ 59
def prefixEnd_3608305 : Nat := 4983230072969 + 3 ^ 40 * 3608305 * 2
def baseEnd_3608305 : Nat := 22874010037303829923373

theorem tailTrace_3608305 : CollatzResearch.WordTrace tailWord_3608305 prefixEnd_3608305 22874010037303829923373 := by
  unfold tailWord_3608305
  simp only [CollatzResearch.WordTrace]
  refine ⟨131605695192734709276986369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87737130128489806184657579 131605695192734709276986369)
  ·
    refine ⟨98704271394551031957739777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131605695192734709276986369 98704271394551031957739777)
    ·
      refine ⟨74028203545913273968304833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98704271394551031957739777 74028203545913273968304833)
      ·
        refine ⟨55521152659434955476228625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74028203545913273968304833 55521152659434955476228625)
        ·
          refine ⟨41640864494576216607171469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55521152659434955476228625 41640864494576216607171469)
          ·
            refine ⟨15615324185466081227689301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41640864494576216607171469 15615324185466081227689301)
            ·
              refine ⟨22874010037303829923373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 15615324185466081227689301 22874010037303829923373)
              ·
                rfl

theorem cell23_3608305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 11].length) (baseStart_3608305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3608305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3608305 prefixEnd_3608305 := by exact prefixLift 3608305
  have htrace : WordTrace (prefixWord ++ tailWord_3608305) baseStart_3608305 baseEnd_3608305 := by
    simpa [prefixWord, tailWord_3608305, baseEnd_3608305] using wordTrace_append hprefix tailTrace_3608305
  have hstable : (prefixWord ++ tailWord_3608305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608305).length < 2 ^ (prefixWord ++ tailWord_3608305).sum := by decide
  have hdescent : baseEnd_3608305 < baseStart_3608305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608310 : List Nat := [5, 1, 1, 1, 1, 4, 3, 2, 1, 1, 3]
def baseStart_3608310 : Nat := 118140960795 + 3608310 * 2 ^ 59
def prefixEnd_3608310 : Nat := 4983230072969 + 3 ^ 40 * 3608310 * 2
def baseEnd_3608310 : Nat := 1852797380424882704230691

theorem tailTrace_3608310 : CollatzResearch.WordTrace tailWord_3608310 prefixEnd_3608310 1852797380424882704230691 := by
  unfold tailWord_3608310
  simp only [CollatzResearch.WordTrace]
  refine ⟨8225367347357287195682399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87737251705144396753945589 8225367347357287195682399)
  ·
    refine ⟨12338051021035930793523599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8225367347357287195682399 12338051021035930793523599)
    ·
      refine ⟨18507076531553896190285399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12338051021035930793523599 18507076531553896190285399)
      ·
        refine ⟨27760614797330844285428099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18507076531553896190285399 27760614797330844285428099)
        ·
          refine ⟨41640922195996266428142149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27760614797330844285428099 41640922195996266428142149)
          ·
            refine ⟨7807672911749299955276653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41640922195996266428142149 7807672911749299955276653)
            ·
              refine ⟨2927877341905987483228745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7807672911749299955276653 2927877341905987483228745)
              ·
                refine ⟨2195908006429490612421559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2927877341905987483228745 2195908006429490612421559)
                ·
                  refine ⟨3293862009644235918632339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2195908006429490612421559 3293862009644235918632339)
                  ·
                    refine ⟨4940793014466353877948509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3293862009644235918632339 4940793014466353877948509)
                    ·
                      refine ⟨1852797380424882704230691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4940793014466353877948509 1852797380424882704230691)
                      ·
                        rfl

theorem cell23_3608310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3, 2, 1, 1, 3].length) (baseStart_3608310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3608310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3608310 prefixEnd_3608310 := by exact prefixLift 3608310
  have htrace : WordTrace (prefixWord ++ tailWord_3608310) baseStart_3608310 baseEnd_3608310 := by
    simpa [prefixWord, tailWord_3608310, baseEnd_3608310] using wordTrace_append hprefix tailTrace_3608310
  have hstable : (prefixWord ++ tailWord_3608310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608310).length < 2 ^ (prefixWord ++ tailWord_3608310).sum := by decide
  have hdescent : baseEnd_3608310 < baseStart_3608310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608335 : List Nat := [1, 1, 2, 1, 1, 1, 4, 1, 4, 7]
def baseStart_3608335 : Nat := 118140960795 + 3608335 * 2 ^ 59
def prefixEnd_3608335 : Nat := 4983230072969 + 3 ^ 40 * 3608335 * 2
def baseEnd_3608335 : Nat := 617603405813748368806025

theorem tailTrace_3608335 : CollatzResearch.WordTrace tailWord_3608335 prefixEnd_3608335 617603405813748368806025 := by
  unfold tailWord_3608335
  simp only [CollatzResearch.WordTrace]
  refine ⟨131606789382626024400578459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87737859588417349600385639 131606789382626024400578459)
  ·
    refine ⟨197410184073939036600867689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131606789382626024400578459 197410184073939036600867689)
    ·
      refine ⟨148057638055454277450650767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197410184073939036600867689 148057638055454277450650767)
      ·
        refine ⟨222086457083181416175976151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148057638055454277450650767 222086457083181416175976151)
        ·
          refine ⟨333129685624772124263964227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222086457083181416175976151 333129685624772124263964227)
          ·
            refine ⟨499694528437158186395946341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333129685624772124263964227 499694528437158186395946341)
            ·
              refine ⟨93692724081967159949239939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 499694528437158186395946341 93692724081967159949239939)
              ·
                refine ⟨140539086122950739923859909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93692724081967159949239939 140539086122950739923859909)
                ·
                  refine ⟨26351078648053263735723733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 140539086122950739923859909 26351078648053263735723733)
                  ·
                    refine ⟨617603405813748368806025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26351078648053263735723733 617603405813748368806025)
                    ·
                      rfl

theorem cell23_3608335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 7].length) (baseStart_3608335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3608335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3608335 prefixEnd_3608335 := by exact prefixLift 3608335
  have htrace : WordTrace (prefixWord ++ tailWord_3608335) baseStart_3608335 baseEnd_3608335 := by
    simpa [prefixWord, tailWord_3608335, baseEnd_3608335] using wordTrace_append hprefix tailTrace_3608335
  have hstable : (prefixWord ++ tailWord_3608335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608335).length < 2 ^ (prefixWord ++ tailWord_3608335).sum := by decide
  have hdescent : baseEnd_3608335 < baseStart_3608335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608345 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 2, 3, 7]
def baseStart_3608345 : Nat := 118140960795 + 3608345 * 2 ^ 59
def prefixEnd_3608345 : Nat := 4983230072969 + 3 ^ 40 * 3608345 * 2
def baseEnd_3608345 : Nat := 1852815352247790067293029

theorem tailTrace_3608345 : CollatzResearch.WordTrace tailWord_3608345 prefixEnd_3608345 1852815352247790067293029 := by
  unfold tailWord_3608345
  simp only [CollatzResearch.WordTrace]
  refine ⟨131607154112589796108442489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87738102741726530738961659 131607154112589796108442489)
  ·
    refine ⟨98705365584442347081331867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131607154112589796108442489 98705365584442347081331867)
    ·
      refine ⟨148058048376663520621997801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98705365584442347081331867 148058048376663520621997801)
      ·
        refine ⟨111043536282497640466498351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148058048376663520621997801 111043536282497640466498351)
        ·
          refine ⟨166565304423746460699747527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111043536282497640466498351 166565304423746460699747527)
          ·
            refine ⟨249847956635619691049621291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166565304423746460699747527 249847956635619691049621291)
            ·
              refine ⟨374771934953429536574431937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249847956635619691049621291 374771934953429536574431937)
              ·
                refine ⟨281078951215072152430823953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 374771934953429536574431937 281078951215072152430823953)
                ·
                  refine ⟨210809213411304114323117965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 281078951215072152430823953 210809213411304114323117965)
                  ·
                    refine ⟨79053455029239042871169237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 210809213411304114323117965 79053455029239042871169237)
                    ·
                      refine ⟨1852815352247790067293029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 79053455029239042871169237 1852815352247790067293029)
                      ·
                        rfl

theorem cell23_3608345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 3, 7].length) (baseStart_3608345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3608345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3608345 prefixEnd_3608345 := by exact prefixLift 3608345
  have htrace : WordTrace (prefixWord ++ tailWord_3608345) baseStart_3608345 baseEnd_3608345 := by
    simpa [prefixWord, tailWord_3608345, baseEnd_3608345] using wordTrace_append hprefix tailTrace_3608345
  have hstable : (prefixWord ++ tailWord_3608345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608345).length < 2 ^ (prefixWord ++ tailWord_3608345).sum := by decide
  have hdescent : baseEnd_3608345 < baseStart_3608345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608442 : List Nat := [3, 1, 1, 1, 1, 1, 5, 2, 1, 7]
def baseStart_3608442 : Nat := 118140960795 + 3608442 * 2 ^ 59
def prefixEnd_3608442 : Nat := 4983230072969 + 3 ^ 40 * 3608442 * 2
def baseEnd_3608442 : Nat := 617621719957092062593361

theorem tailTrace_3608442 : CollatzResearch.WordTrace tailWord_3608442 prefixEnd_3608442 617621719957092062593361 := by
  unfold tailWord_3608442
  simp only [CollatzResearch.WordTrace]
  refine ⟨32902672998309595418680895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87740461328825587783149053 32902672998309595418680895)
  ·
    refine ⟨49354009497464393128021343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32902672998309595418680895 49354009497464393128021343)
    ·
      refine ⟨74031014246196589692032015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49354009497464393128021343 74031014246196589692032015)
      ·
        refine ⟨111046521369294884538048023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74031014246196589692032015 111046521369294884538048023)
        ·
          refine ⟨166569782053942326807072035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111046521369294884538048023 166569782053942326807072035)
          ·
            refine ⟨249854673080913490210608053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166569782053942326807072035 249854673080913490210608053)
            ·
              refine ⟨23423875601335639707244505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 249854673080913490210608053 23423875601335639707244505)
              ·
                refine ⟨17567906701001729780433379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23423875601335639707244505 17567906701001729780433379)
                ·
                  refine ⟨26351860051502594670650069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17567906701001729780433379 26351860051502594670650069)
                  ·
                    refine ⟨617621719957092062593361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26351860051502594670650069 617621719957092062593361)
                    ·
                      rfl

theorem cell23_3608442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 1, 7].length) (baseStart_3608442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3608442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3608442 prefixEnd_3608442 := by exact prefixLift 3608442
  have htrace : WordTrace (prefixWord ++ tailWord_3608442) baseStart_3608442 baseEnd_3608442 := by
    simpa [prefixWord, tailWord_3608442, baseEnd_3608442] using wordTrace_append hprefix tailTrace_3608442
  have hstable : (prefixWord ++ tailWord_3608442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608442).length < 2 ^ (prefixWord ++ tailWord_3608442).sum := by decide
  have hdescent : baseEnd_3608442 < baseStart_3608442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608446 : List Nat := [4, 2, 3, 1, 1, 1, 2, 2, 7]
def baseStart_3608446 : Nat := 118140960795 + 3608446 * 2 ^ 59
def prefixEnd_3608446 : Nat := 4983230072969 + 3 ^ 40 * 3608446 * 2
def baseEnd_3608446 : Nat := 205874134865988241347785

theorem tailTrace_3608446 : CollatzResearch.WordTrace tailWord_3608446 prefixEnd_3608446 205874134865988241347785 := by
  unfold tailWord_3608446
  simp only [CollatzResearch.WordTrace]
  refine ⟨16451354735652986294733649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87740558590149260238579461 16451354735652986294733649)
  ·
    refine ⟨12338516051739739721050237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16451354735652986294733649 12338516051739739721050237)
    ·
      refine ⟨4626943519402402395393839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12338516051739739721050237 4626943519402402395393839)
      ·
        refine ⟨6940415279103603593090759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4626943519402402395393839 6940415279103603593090759)
        ·
          refine ⟨10410622918655405389636139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6940415279103603593090759 10410622918655405389636139)
          ·
            refine ⟨15615934377983108084454209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10410622918655405389636139 15615934377983108084454209)
            ·
              refine ⟨11711950783487331063340657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15615934377983108084454209 11711950783487331063340657)
              ·
                refine ⟨8783963087615498297505493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11711950783487331063340657 8783963087615498297505493)
                ·
                  refine ⟨205874134865988241347785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8783963087615498297505493 205874134865988241347785)
                  ·
                    rfl

theorem cell23_3608446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 2, 7].length) (baseStart_3608446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3608446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3608446 prefixEnd_3608446 := by exact prefixLift 3608446
  have htrace : WordTrace (prefixWord ++ tailWord_3608446) baseStart_3608446 baseEnd_3608446 := by
    simpa [prefixWord, tailWord_3608446, baseEnd_3608446] using wordTrace_append hprefix tailTrace_3608446
  have hstable : (prefixWord ++ tailWord_3608446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608446).length < 2 ^ (prefixWord ++ tailWord_3608446).sum := by decide
  have hdescent : baseEnd_3608446 < baseStart_3608446 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608476 : List Nat := [2, 2, 3, 3, 1, 2, 1, 2, 2, 5]
def baseStart_3608476 : Nat := 118140960795 + 3608476 * 2 ^ 59
def prefixEnd_3608476 : Nat := 4983230072969 + 3 ^ 40 * 3608476 * 2
def baseEnd_3608476 : Nat := 617627539404509684918309

theorem tailTrace_3608476 : CollatzResearch.WordTrace tailWord_3608476 prefixEnd_3608476 617627539404509684918309 := by
  unfold tailWord_3608476
  simp only [CollatzResearch.WordTrace]
  refine ⟨65805966037557602740730641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87741288050076803654307521 65805966037557602740730641)
  ·
    refine ⟨49354474528168202055547981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65805966037557602740730641 49354474528168202055547981)
    ·
      refine ⟨18507927948063075770830493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49354474528168202055547981 18507927948063075770830493)
      ·
        refine ⟨6940472980523653414061435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18507927948063075770830493 6940472980523653414061435)
        ·
          refine ⟨10410709470785480121092153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6940472980523653414061435 10410709470785480121092153)
          ·
            refine ⟨7808032103089110090819115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10410709470785480121092153 7808032103089110090819115)
            ·
              refine ⟨11712048154633665136228673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7808032103089110090819115 11712048154633665136228673)
              ·
                refine ⟨8784036115975248852171505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11712048154633665136228673 8784036115975248852171505)
                ·
                  refine ⟨6588027086981436639128629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8784036115975248852171505 6588027086981436639128629)
                  ·
                    refine ⟨617627539404509684918309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6588027086981436639128629 617627539404509684918309)
                    ·
                      rfl

theorem cell23_3608476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_3608476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3608476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3608476 prefixEnd_3608476 := by exact prefixLift 3608476
  have htrace : WordTrace (prefixWord ++ tailWord_3608476) baseStart_3608476 baseEnd_3608476 := by
    simpa [prefixWord, tailWord_3608476, baseEnd_3608476] using wordTrace_append hprefix tailTrace_3608476
  have hstable : (prefixWord ++ tailWord_3608476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608476).length < 2 ^ (prefixWord ++ tailWord_3608476).sum := by decide
  have hdescent : baseEnd_3608476 < baseStart_3608476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608489 : List Nat := [1, 2, 1, 1, 1, 1, 4, 5, 3, 4]
def baseStart_3608489 : Nat := 118140960795 + 3608489 * 2 ^ 59
def prefixEnd_3608489 : Nat := 4983230072969 + 3 ^ 40 * 3608489 * 2
def baseEnd_3608489 : Nat := 617629764487345834630789

theorem tailTrace_3608489 : CollatzResearch.WordTrace tailWord_3608489 prefixEnd_3608489 617629764487345834630789 := by
  unfold tailWord_3608489
  simp only [CollatzResearch.WordTrace]
  refine ⟨131612406224068108701684521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87741604149378739134456347 131612406224068108701684521)
  ·
    refine ⟨98709304668051081526263391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131612406224068108701684521 98709304668051081526263391)
    ·
      refine ⟨148063957002076622289395087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98709304668051081526263391 148063957002076622289395087)
      ·
        refine ⟨222095935503114933434092631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148063957002076622289395087 222095935503114933434092631)
        ·
          refine ⟨333143903254672400151138947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222095935503114933434092631 333143903254672400151138947)
          ·
            refine ⟨499715854882008600226708421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333143903254672400151138947 499715854882008600226708421)
            ·
              refine ⟨93696722790376612542507829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 499715854882008600226708421 93696722790376612542507829)
              ·
                refine ⟨8784067761597807425860109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93696722790376612542507829 8784067761597807425860109)
                ·
                  refine ⟨3294025410599177784697541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8784067761597807425860109 3294025410599177784697541)
                  ·
                    refine ⟨617629764487345834630789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3294025410599177784697541 617629764487345834630789)
                    ·
                      rfl

theorem cell23_3608489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5, 3, 4].length) (baseStart_3608489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3608489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3608489 prefixEnd_3608489 := by exact prefixLift 3608489
  have htrace : WordTrace (prefixWord ++ tailWord_3608489) baseStart_3608489 baseEnd_3608489 := by
    simpa [prefixWord, tailWord_3608489, baseEnd_3608489] using wordTrace_append hprefix tailTrace_3608489
  have hstable : (prefixWord ++ tailWord_3608489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608489).length < 2 ^ (prefixWord ++ tailWord_3608489).sum := by decide
  have hdescent : baseEnd_3608489 < baseStart_3608489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608499 : List Nat := [1, 1, 1, 2, 3, 1, 3, 2, 4, 2, 3]
def baseStart_3608499 : Nat := 118140960795 + 3608499 * 2 ^ 59
def prefixEnd_3608499 : Nat := 4983230072969 + 3 ^ 40 * 3608499 * 2
def baseEnd_3608499 : Nat := 1852894428268582464767321

theorem tailTrace_3608499 : CollatzResearch.WordTrace tailWord_3608499 prefixEnd_3608499 1852894428268582464767321 := by
  unfold tailWord_3608499
  simp only [CollatzResearch.WordTrace]
  refine ⟨131612770954031880409548551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87741847302687920273032367 131612770954031880409548551)
  ·
    refine ⟨197419156431047820614322827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131612770954031880409548551 197419156431047820614322827)
    ·
      refine ⟨296128734646571730921484241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197419156431047820614322827 296128734646571730921484241)
      ·
        refine ⟨222096550984928798191113181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296128734646571730921484241 222096550984928798191113181)
        ·
          refine ⟨83286206619348299321667443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222096550984928798191113181 83286206619348299321667443)
          ·
            refine ⟨124929309929022448982501165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83286206619348299321667443 124929309929022448982501165)
            ·
              refine ⟨46848491223383418368437937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124929309929022448982501165 46848491223383418368437937)
              ·
                refine ⟨35136368417537563776328453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46848491223383418368437937 35136368417537563776328453)
                ·
                  refine ⟨6588069078288293208061585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35136368417537563776328453 6588069078288293208061585)
                  ·
                    refine ⟨4941051808716219906046189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6588069078288293208061585 4941051808716219906046189)
                    ·
                      refine ⟨1852894428268582464767321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4941051808716219906046189 1852894428268582464767321)
                      ·
                        rfl

theorem cell23_3608499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 4, 2, 3].length) (baseStart_3608499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3608499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3608499 prefixEnd_3608499 := by exact prefixLift 3608499
  have htrace : WordTrace (prefixWord ++ tailWord_3608499) baseStart_3608499 baseEnd_3608499 := by
    simpa [prefixWord, tailWord_3608499, baseEnd_3608499] using wordTrace_append hprefix tailTrace_3608499
  have hstable : (prefixWord ++ tailWord_3608499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608499).length < 2 ^ (prefixWord ++ tailWord_3608499).sum := by decide
  have hdescent : baseEnd_3608499 < baseStart_3608499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608556 : List Nat := [2, 2, 1, 1, 2, 1, 1, 4, 4, 3, 2]
def baseStart_3608556 : Nat := 118140960795 + 3608556 * 2 ^ 59
def prefixEnd_3608556 : Nat := 4983230072969 + 3 ^ 40 * 3608556 * 2
def baseEnd_3608556 : Nat := 1852923696665888741754559

theorem tailTrace_3608556 : CollatzResearch.WordTrace tailWord_3608556 prefixEnd_3608556 1852923696665888741754559 := by
  unfold tailWord_3608556
  simp only [CollatzResearch.WordTrace]
  refine ⟨65807424957412689572186761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87743233276550252762915681 65807424957412689572186761)
  ·
    refine ⟨49355568718059517179140071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65807424957412689572186761 49355568718059517179140071)
    ·
      refine ⟨74033353077089275768710107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49355568718059517179140071 74033353077089275768710107)
      ·
        refine ⟨111050029615633913653065161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74033353077089275768710107 111050029615633913653065161)
        ·
          refine ⟨83287522211725435239798871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111050029615633913653065161 83287522211725435239798871)
          ·
            refine ⟨124931283317588152859698307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83287522211725435239798871 124931283317588152859698307)
            ·
              refine ⟨187396924976382229289547461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124931283317588152859698307 187396924976382229289547461)
              ·
                refine ⟨35136923433071667991790149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 187396924976382229289547461 35136923433071667991790149)
                ·
                  refine ⟨6588173143700937748460653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35136923433071667991790149 6588173143700937748460653)
                  ·
                    refine ⟨2470564928887851655672745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6588173143700937748460653 2470564928887851655672745)
                    ·
                      refine ⟨1852923696665888741754559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2470564928887851655672745 1852923696665888741754559)
                      ·
                        rfl

theorem cell23_3608556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 3, 2].length) (baseStart_3608556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3608556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3608556 prefixEnd_3608556 := by exact prefixLift 3608556
  have htrace : WordTrace (prefixWord ++ tailWord_3608556) baseStart_3608556 baseEnd_3608556 := by
    simpa [prefixWord, tailWord_3608556, baseEnd_3608556] using wordTrace_append hprefix tailTrace_3608556
  have hstable : (prefixWord ++ tailWord_3608556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608556).length < 2 ^ (prefixWord ++ tailWord_3608556).sum := by decide
  have hdescent : baseEnd_3608556 < baseStart_3608556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608573 : List Nat := [1, 4, 1, 1, 1, 2, 5, 1, 2, 3, 2]
def baseStart_3608573 : Nat := 118140960795 + 3608573 * 2 ^ 59
def prefixEnd_3608573 : Nat := 4983230072969 + 3 ^ 40 * 3608573 * 2
def baseEnd_3608573 : Nat := 1852932425837015175241981

theorem tailTrace_3608573 : CollatzResearch.WordTrace tailWord_3608573 prefixEnd_3608573 1852932425837015175241981 := by
  unfold tailWord_3608573
  simp only [CollatzResearch.WordTrace]
  refine ⟨131615469955763791047742373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87743646637175860698494915 131615469955763791047742373)
  ·
    refine ⟨24677900616705710821451695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131615469955763791047742373 24677900616705710821451695)
    ·
      refine ⟨37016850925058566232177543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24677900616705710821451695 37016850925058566232177543)
      ·
        refine ⟨55525276387587849348266315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37016850925058566232177543 55525276387587849348266315)
        ·
          refine ⟨83287914581381774022399473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55525276387587849348266315 83287914581381774022399473)
          ·
            refine ⟨62465935936036330516799605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83287914581381774022399473 62465935936036330516799605)
            ·
              refine ⟨5856181494003405985949963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62465935936036330516799605 5856181494003405985949963)
              ·
                refine ⟨8784272241005108978924945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5856181494003405985949963 8784272241005108978924945)
                ·
                  refine ⟨6588204180753831734193709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8784272241005108978924945 6588204180753831734193709)
                  ·
                    refine ⟨2470576567782686900322641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6588204180753831734193709 2470576567782686900322641)
                    ·
                      refine ⟨1852932425837015175241981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2470576567782686900322641 1852932425837015175241981)
                      ·
                        rfl

theorem cell23_3608573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 1, 2, 3, 2].length) (baseStart_3608573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3608573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3608573 prefixEnd_3608573 := by exact prefixLift 3608573
  have htrace : WordTrace (prefixWord ++ tailWord_3608573) baseStart_3608573 baseEnd_3608573 := by
    simpa [prefixWord, tailWord_3608573, baseEnd_3608573] using wordTrace_append hprefix tailTrace_3608573
  have hstable : (prefixWord ++ tailWord_3608573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608573).length < 2 ^ (prefixWord ++ tailWord_3608573).sum := by decide
  have hdescent : baseEnd_3608573 < baseStart_3608573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608583 : List Nat := [1, 1, 4, 3, 1, 2, 4, 1, 1, 5]
def baseStart_3608583 : Nat := 118140960795 + 3608583 * 2 ^ 59
def prefixEnd_3608583 : Nat := 4983230072969 + 3 ^ 40 * 3608583 * 2
def baseEnd_3608583 : Nat := 617645853547853378705645

theorem tailTrace_3608583 : CollatzResearch.WordTrace tailWord_3608583 prefixEnd_3608583 617645853547853378705645 := by
  unfold tailWord_3608583
  simp only [CollatzResearch.WordTrace]
  refine ⟨131615834685727562755606403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87743889790485041837070935 131615834685727562755606403)
  ·
    refine ⟨197423752028591344133409605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131615834685727562755606403 197423752028591344133409605)
    ·
      refine ⟨37016953505360877025014301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 197423752028591344133409605 37016953505360877025014301)
      ·
        refine ⟨13881357564510328884380363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37016953505360877025014301 13881357564510328884380363)
        ·
          refine ⟨20822036346765493326570545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13881357564510328884380363 20822036346765493326570545)
          ·
            refine ⟨15616527260074119994927909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20822036346765493326570545 15616527260074119994927909)
            ·
              refine ⟨2928098861263897499048983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15616527260074119994927909 2928098861263897499048983)
              ·
                refine ⟨4392148291895846248573475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2928098861263897499048983 4392148291895846248573475)
                ·
                  refine ⟨6588222437843769372860213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4392148291895846248573475 6588222437843769372860213)
                  ·
                    refine ⟨617645853547853378705645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6588222437843769372860213 617645853547853378705645)
                    ·
                      rfl

theorem cell23_3608583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4, 1, 1, 5].length) (baseStart_3608583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3608583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3608583 prefixEnd_3608583 := by exact prefixLift 3608583
  have htrace : WordTrace (prefixWord ++ tailWord_3608583) baseStart_3608583 baseEnd_3608583 := by
    simpa [prefixWord, tailWord_3608583, baseEnd_3608583] using wordTrace_append hprefix tailTrace_3608583
  have hstable : (prefixWord ++ tailWord_3608583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608583).length < 2 ^ (prefixWord ++ tailWord_3608583).sum := by decide
  have hdescent : baseEnd_3608583 < baseStart_3608583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608626 : List Nat := [3, 2, 1, 1, 2, 3, 4, 7]
def baseStart_3608626 : Nat := 118140960795 + 3608626 * 2 ^ 59
def prefixEnd_3608626 : Nat := 4983230072969 + 3 ^ 40 * 3608626 * 2
def baseEnd_3608626 : Nat := 68628134826359387699231

theorem tailTrace_3608626 : CollatzResearch.WordTrace tailWord_3608626 prefixEnd_3608626 68628134826359387699231 := by
  unfold tailWord_3608626
  simp only [CollatzResearch.WordTrace]
  refine ⟨32904350756142945274855433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87744935349714520732947821 32904350756142945274855433)
  ·
    refine ⟨24678263067107208956141575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32904350756142945274855433 24678263067107208956141575)
    ·
      refine ⟨37017394600660813434212363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24678263067107208956141575 37017394600660813434212363)
      ·
        refine ⟨55526091900991220151318545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37017394600660813434212363 55526091900991220151318545)
        ·
          refine ⟨41644568925743415113488909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55526091900991220151318545 41644568925743415113488909)
          ·
            refine ⟨15616713347153780667558341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41644568925743415113488909 15616713347153780667558341)
            ·
              refine ⟨2928133752591333875167189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15616713347153780667558341 2928133752591333875167189)
              ·
                refine ⟨68628134826359387699231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2928133752591333875167189 68628134826359387699231)
                ·
                  rfl

theorem cell23_3608626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4, 7].length) (baseStart_3608626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3608626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3608626 prefixEnd_3608626 := by exact prefixLift 3608626
  have htrace : WordTrace (prefixWord ++ tailWord_3608626) baseStart_3608626 baseEnd_3608626 := by
    simpa [prefixWord, tailWord_3608626, baseEnd_3608626] using wordTrace_append hprefix tailTrace_3608626
  have hstable : (prefixWord ++ tailWord_3608626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608626).length < 2 ^ (prefixWord ++ tailWord_3608626).sum := by decide
  have hdescent : baseEnd_3608626 < baseStart_3608626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608636 : List Nat := [2, 2, 2, 2, 2, 1, 2, 1, 3, 3, 3]
def baseStart_3608636 : Nat := 118140960795 + 3608636 * 2 ^ 59
def prefixEnd_3608636 : Nat := 4983230072969 + 3 ^ 40 * 3608636 * 2
def baseEnd_3608636 : Nat := 1852964775118248428754191

theorem tailTrace_3608636 : CollatzResearch.WordTrace tailWord_3608636 prefixEnd_3608636 1852964775118248428754191 := by
  unfold tailWord_3608636
  simp only [CollatzResearch.WordTrace]
  refine ⟨65808883877267776403642881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87745178503023701871523841 65808883877267776403642881)
  ·
    refine ⟨49356662907950832302732161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65808883877267776403642881 49356662907950832302732161)
    ·
      refine ⟨37017497180963124227049121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49356662907950832302732161 37017497180963124227049121)
      ·
        refine ⟨27763122885722343170286841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37017497180963124227049121 27763122885722343170286841)
        ·
          refine ⟨20822342164291757377715131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27763122885722343170286841 20822342164291757377715131)
          ·
            refine ⟨31233513246437636066572697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20822342164291757377715131 31233513246437636066572697)
            ·
              refine ⟨23425134934828227049929523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31233513246437636066572697 23425134934828227049929523)
              ·
                refine ⟨35137702402242340574894285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23425134934828227049929523 35137702402242340574894285)
                ·
                  refine ⟨13176638400840877715585357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35137702402242340574894285 13176638400840877715585357)
                  ·
                    refine ⟨4941239400315329143344509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13176638400840877715585357 4941239400315329143344509)
                    ·
                      refine ⟨1852964775118248428754191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4941239400315329143344509 1852964775118248428754191)
                      ·
                        rfl

theorem cell23_3608636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_3608636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3608636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3608636 prefixEnd_3608636 := by exact prefixLift 3608636
  have htrace : WordTrace (prefixWord ++ tailWord_3608636) baseStart_3608636 baseEnd_3608636 := by
    simpa [prefixWord, tailWord_3608636, baseEnd_3608636] using wordTrace_append hprefix tailTrace_3608636
  have hstable : (prefixWord ++ tailWord_3608636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608636).length < 2 ^ (prefixWord ++ tailWord_3608636).sum := by decide
  have hdescent : baseEnd_3608636 < baseStart_3608636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608649 : List Nat := [1, 2, 1, 1, 2, 2, 3, 2, 2, 2, 5]
def baseStart_3608649 : Nat := 118140960795 + 3608649 * 2 ^ 59
def prefixEnd_3608649 : Nat := 4983230072969 + 3 ^ 40 * 3608649 * 2
def baseEnd_3608649 : Nat := 1852971450366756877891631

theorem tailTrace_3608649 : CollatzResearch.WordTrace tailWord_3608649 prefixEnd_3608649 1852971450366756877891631 := by
  unfold tailWord_3608649
  simp only [CollatzResearch.WordTrace]
  refine ⟨131618241903488456027509001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87745494602325637351672667 131618241903488456027509001)
  ·
    refine ⟨98713681427616342020631751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131618241903488456027509001 98713681427616342020631751)
    ·
      refine ⟨148070522141424513030947627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98713681427616342020631751 148070522141424513030947627)
      ·
        refine ⟨222105783212136769546421441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148070522141424513030947627 222105783212136769546421441)
        ·
          refine ⟨166579337409102577159816081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222105783212136769546421441 166579337409102577159816081)
          ·
            refine ⟨124934503056826932869862061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166579337409102577159816081 124934503056826932869862061)
            ·
              refine ⟨46850438646310099826198273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124934503056826932869862061 46850438646310099826198273)
              ·
                refine ⟨35137828984732574869648705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46850438646310099826198273 35137828984732574869648705)
                ·
                  refine ⟨26353371738549431152236529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35137828984732574869648705 26353371738549431152236529)
                  ·
                    refine ⟨19765028803912073364177397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26353371738549431152236529 19765028803912073364177397)
                    ·
                      refine ⟨1852971450366756877891631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19765028803912073364177397 1852971450366756877891631)
                      ·
                        rfl

theorem cell23_3608649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 2, 5].length) (baseStart_3608649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3608649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3608649 prefixEnd_3608649 := by exact prefixLift 3608649
  have htrace : WordTrace (prefixWord ++ tailWord_3608649) baseStart_3608649 baseEnd_3608649 := by
    simpa [prefixWord, tailWord_3608649, baseEnd_3608649] using wordTrace_append hprefix tailTrace_3608649
  have hstable : (prefixWord ++ tailWord_3608649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608649).length < 2 ^ (prefixWord ++ tailWord_3608649).sum := by decide
  have hdescent : baseEnd_3608649 < baseStart_3608649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608654 : List Nat := [4, 1, 1, 1, 1, 5, 3, 2, 1, 2, 2]
def baseStart_3608654 : Nat := 118140960795 + 3608654 * 2 ^ 59
def prefixEnd_3608654 : Nat := 4983230072969 + 3 ^ 40 * 3608654 * 2
def baseEnd_3608654 : Nat := 1852974017770029358329109

theorem tailTrace_3608654 : CollatzResearch.WordTrace tailWord_3608654 prefixEnd_3608654 1852974017770029358329109 := by
  unfold tailWord_3608654
  simp only [CollatzResearch.WordTrace]
  refine ⟨16452303033558792735180127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87745616178980227920960677 16452303033558792735180127)
  ·
    refine ⟨24678454550338189102770191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16452303033558792735180127 24678454550338189102770191)
    ·
      refine ⟨37017681825507283654155287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24678454550338189102770191 37017681825507283654155287)
      ·
        refine ⟨55526522738260925481232931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37017681825507283654155287 55526522738260925481232931)
        ·
          refine ⟨83289784107391388221849397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55526522738260925481232931 83289784107391388221849397)
          ·
            refine ⟨7808417260067942645798381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83289784107391388221849397 7808417260067942645798381)
            ·
              refine ⟨2928156472525478492174393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7808417260067942645798381 2928156472525478492174393)
              ·
                refine ⟨2196117354394108869130795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2928156472525478492174393 2196117354394108869130795)
                ·
                  refine ⟨3294176031591163303696193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2196117354394108869130795 3294176031591163303696193)
                  ·
                    refine ⟨2470632023693372477772145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3294176031591163303696193 2470632023693372477772145)
                    ·
                      refine ⟨1852974017770029358329109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2470632023693372477772145 1852974017770029358329109)
                      ·
                        rfl

theorem cell23_3608654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3, 2, 1, 2, 2].length) (baseStart_3608654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3608654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3608654 prefixEnd_3608654 := by exact prefixLift 3608654
  have htrace : WordTrace (prefixWord ++ tailWord_3608654) baseStart_3608654 baseEnd_3608654 := by
    simpa [prefixWord, tailWord_3608654, baseEnd_3608654] using wordTrace_append hprefix tailTrace_3608654
  have hstable : (prefixWord ++ tailWord_3608654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608654).length < 2 ^ (prefixWord ++ tailWord_3608654).sum := by decide
  have hdescent : baseEnd_3608654 < baseStart_3608654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608674 : List Nat := [3, 3, 2, 2, 3, 1, 1, 2, 1, 2, 3]
def baseStart_3608674 : Nat := 118140960795 + 3608674 * 2 ^ 59
def prefixEnd_3608674 : Nat := 4983230072969 + 3 ^ 40 * 3608674 * 2
def baseEnd_3608674 : Nat := 1852984287383119280079017

theorem tailTrace_3608674 : CollatzResearch.WordTrace tailWord_3608674 prefixEnd_3608674 1852984287383119280079017 := by
  unfold tailWord_3608674
  simp only [CollatzResearch.WordTrace]
  refine ⟨32904788432099471324292269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87746102485598590198112717 32904788432099471324292269)
  ·
    refine ⟨12339295662037301746609601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32904788432099471324292269 12339295662037301746609601)
    ·
      refine ⟨9254471746527976309957201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12339295662037301746609601 9254471746527976309957201)
      ·
        refine ⟨6940853809895982232467901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9254471746527976309957201 6940853809895982232467901)
        ·
          refine ⟨2602820178710993337175463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6940853809895982232467901 2602820178710993337175463)
          ·
            refine ⟨3904230268066490005763195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2602820178710993337175463 3904230268066490005763195)
            ·
              refine ⟨5856345402099735008644793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3904230268066490005763195 5856345402099735008644793)
              ·
                refine ⟨4392259051574801256483595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5856345402099735008644793 4392259051574801256483595)
                ·
                  refine ⟨6588388577362201884725393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4392259051574801256483595 6588388577362201884725393)
                  ·
                    refine ⟨4941291433021651413544045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6588388577362201884725393 4941291433021651413544045)
                    ·
                      refine ⟨1852984287383119280079017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4941291433021651413544045 1852984287383119280079017)
                      ·
                        rfl

theorem cell23_3608674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_3608674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3608674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3608674 prefixEnd_3608674 := by exact prefixLift 3608674
  have htrace : WordTrace (prefixWord ++ tailWord_3608674) baseStart_3608674 baseEnd_3608674 := by
    simpa [prefixWord, tailWord_3608674, baseEnd_3608674] using wordTrace_append hprefix tailTrace_3608674
  have hstable : (prefixWord ++ tailWord_3608674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608674).length < 2 ^ (prefixWord ++ tailWord_3608674).sum := by decide
  have hdescent : baseEnd_3608674 < baseStart_3608674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608697 : List Nat := [1, 2, 1, 3, 4, 2, 3, 1, 1, 3, 2]
def baseStart_3608697 : Nat := 118140960795 + 3608697 * 2 ^ 59
def prefixEnd_3608697 : Nat := 4983230072969 + 3 ^ 40 * 3608697 * 2
def baseEnd_3608697 : Nat := 1852996097438172690091411

theorem tailTrace_3608697 : CollatzResearch.WordTrace tailWord_3608697 prefixEnd_3608697 1852996097438172690091411 := by
  unfold tailWord_3608697
  simp only [CollatzResearch.WordTrace]
  refine ⟨131619992607314560225256345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87746661738209706816837563 131619992607314560225256345)
  ·
    refine ⟨98714994455485920168942259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131619992607314560225256345 98714994455485920168942259)
    ·
      refine ⟨148072491683228880253413389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98714994455485920168942259 148072491683228880253413389)
      ·
        refine ⟨55527184381210830095030021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148072491683228880253413389 55527184381210830095030021)
        ·
          refine ⟨10411347071477030642818129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55527184381210830095030021 10411347071477030642818129)
          ·
            refine ⟨7808510303607772982113597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10411347071477030642818129 7808510303607772982113597)
            ·
              refine ⟨2928191363852914868292599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7808510303607772982113597 2928191363852914868292599)
              ·
                refine ⟨4392287045779372302438899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2928191363852914868292599 4392287045779372302438899)
                ·
                  refine ⟨6588430568669058453658349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4392287045779372302438899 6588430568669058453658349)
                  ·
                    refine ⟨2470661463250896920121881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6588430568669058453658349 2470661463250896920121881)
                    ·
                      refine ⟨1852996097438172690091411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2470661463250896920121881 1852996097438172690091411)
                      ·
                        rfl

theorem cell23_3608697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3, 1, 1, 3, 2].length) (baseStart_3608697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3608697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3608697 prefixEnd_3608697 := by exact prefixLift 3608697
  have htrace : WordTrace (prefixWord ++ tailWord_3608697) baseStart_3608697 baseEnd_3608697 := by
    simpa [prefixWord, tailWord_3608697, baseEnd_3608697] using wordTrace_append hprefix tailTrace_3608697
  have hstable : (prefixWord ++ tailWord_3608697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608697).length < 2 ^ (prefixWord ++ tailWord_3608697).sum := by decide
  have hdescent : baseEnd_3608697 < baseStart_3608697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608719 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 6]
def baseStart_3608719 : Nat := 118140960795 + 3608719 * 2 ^ 59
def prefixEnd_3608719 : Nat := 4983230072969 + 3 ^ 40 * 3608719 * 2
def baseEnd_3608719 : Nat := 1853007394012571604016309

theorem tailTrace_3608719 : CollatzResearch.WordTrace tailWord_3608719 prefixEnd_3608719 1853007394012571604016309 := by
  unfold tailWord_3608719
  simp only [CollatzResearch.WordTrace]
  refine ⟨131620795013234857982557211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87747196675489905321704807 131620795013234857982557211)
  ·
    refine ⟨197431192519852286973835817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131620795013234857982557211 197431192519852286973835817)
    ·
      refine ⟨148073394389889215230376863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197431192519852286973835817 148073394389889215230376863)
      ·
        refine ⟨222110091584833822845565295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148073394389889215230376863 222110091584833822845565295)
        ·
          refine ⟨333165137377250734268347943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222110091584833822845565295 333165137377250734268347943)
          ·
            refine ⟨499747706065876101402521915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333165137377250734268347943 499747706065876101402521915)
            ·
              refine ⟨749621559098814152103782873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 499747706065876101402521915 749621559098814152103782873)
              ·
                refine ⟨562216169324110614077837155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 749621559098814152103782873 562216169324110614077837155)
                ·
                  refine ⟨843324253986165921116755733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 562216169324110614077837155 843324253986165921116755733)
                  ·
                    refine ⟨39530824405601527552347925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 843324253986165921116755733 39530824405601527552347925)
                    ·
                      refine ⟨1853007394012571604016309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39530824405601527552347925 1853007394012571604016309)
                      ·
                        rfl

theorem cell23_3608719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 6].length) (baseStart_3608719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3608719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3608719 prefixEnd_3608719 := by exact prefixLift 3608719
  have htrace : WordTrace (prefixWord ++ tailWord_3608719) baseStart_3608719 baseEnd_3608719 := by
    simpa [prefixWord, tailWord_3608719, baseEnd_3608719] using wordTrace_append hprefix tailTrace_3608719
  have hstable : (prefixWord ++ tailWord_3608719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608719).length < 2 ^ (prefixWord ++ tailWord_3608719).sum := by decide
  have hdescent : baseEnd_3608719 < baseStart_3608719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608783 : List Nat := [1, 1, 2, 1, 1, 3, 3, 3, 2, 4, 2]
def baseStart_3608783 : Nat := 118140960795 + 3608783 * 2 ^ 59
def prefixEnd_3608783 : Nat := 4983230072969 + 3 ^ 40 * 3608783 * 2
def baseEnd_3608783 : Nat := 1853040256774459353616015

theorem tailTrace_3608783 : CollatzResearch.WordTrace tailWord_3608783 prefixEnd_3608783 1853040256774459353616015 := by
  unfold tailWord_3608783
  simp only [CollatzResearch.WordTrace]
  refine ⟨131623129285002996912887003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87748752856668664608591335 131623129285002996912887003)
  ·
    refine ⟨197434693927504495369330505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131623129285002996912887003 197434693927504495369330505)
    ·
      refine ⟨148076020445628371526997879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197434693927504495369330505 148076020445628371526997879)
      ·
        refine ⟨222114030668442557290496819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148076020445628371526997879 222114030668442557290496819)
        ·
          refine ⟨333171046002663835935745229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222114030668442557290496819 333171046002663835935745229)
          ·
            refine ⟨124939142250998938475904461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 333171046002663835935745229 124939142250998938475904461)
            ·
              refine ⟨46852178344124601928464173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124939142250998938475904461 46852178344124601928464173)
              ·
                refine ⟨17569566879046725723174065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46852178344124601928464173 17569566879046725723174065)
                ·
                  refine ⟨13177175159285044292380549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17569566879046725723174065 13177175159285044292380549)
                  ·
                    refine ⟨2470720342365945804821353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13177175159285044292380549 2470720342365945804821353)
                    ·
                      refine ⟨1853040256774459353616015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2470720342365945804821353 1853040256774459353616015)
                      ·
                        rfl

theorem cell23_3608783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 2, 4, 2].length) (baseStart_3608783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3608783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3608783 prefixEnd_3608783 := by exact prefixLift 3608783
  have htrace : WordTrace (prefixWord ++ tailWord_3608783) baseStart_3608783 baseEnd_3608783 := by
    simpa [prefixWord, tailWord_3608783, baseEnd_3608783] using wordTrace_append hprefix tailTrace_3608783
  have hstable : (prefixWord ++ tailWord_3608783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608783).length < 2 ^ (prefixWord ++ tailWord_3608783).sum := by decide
  have hdescent : baseEnd_3608783 < baseStart_3608783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608793 : List Nat := [1, 2, 1, 2, 3, 1, 4, 2, 3, 4]
def baseStart_3608793 : Nat := 118140960795 + 3608793 * 2 ^ 59
def prefixEnd_3608793 : Nat := 4983230072969 + 3 ^ 40 * 3608793 * 2
def baseEnd_3608793 : Nat := 617681797193668104830323

theorem tailTrace_3608793 : CollatzResearch.WordTrace tailWord_3608793 prefixEnd_3608793 617681797193668104830323 := by
  unfold tailWord_3608793
  simp only [CollatzResearch.WordTrace]
  refine ⟨131623494014966768620751033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87748996009977845747167355 131623494014966768620751033)
  ·
    refine ⟨98717620511225076465563275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131623494014966768620751033 98717620511225076465563275)
    ·
      refine ⟨148076430766837614698344913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98717620511225076465563275 148076430766837614698344913)
      ·
        refine ⟨111057323075128211023758685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148076430766837614698344913 111057323075128211023758685)
        ·
          refine ⟨41646496153173079133909507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111057323075128211023758685 41646496153173079133909507)
          ·
            refine ⟨62469744229759618700864261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41646496153173079133909507 62469744229759618700864261)
            ·
              refine ⟨11713077043079928506412049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62469744229759618700864261 11713077043079928506412049)
              ·
                refine ⟨8784807782309946379809037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11713077043079928506412049 8784807782309946379809037)
                ·
                  refine ⟨3294302918366229892428389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8784807782309946379809037 3294302918366229892428389)
                  ·
                    refine ⟨617681797193668104830323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3294302918366229892428389 617681797193668104830323)
                    ·
                      rfl

theorem cell23_3608793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 2, 3, 4].length) (baseStart_3608793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3608793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3608793 prefixEnd_3608793 := by exact prefixLift 3608793
  have htrace : WordTrace (prefixWord ++ tailWord_3608793) baseStart_3608793 baseEnd_3608793 := by
    simpa [prefixWord, tailWord_3608793, baseEnd_3608793] using wordTrace_append hprefix tailTrace_3608793
  have hstable : (prefixWord ++ tailWord_3608793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608793).length < 2 ^ (prefixWord ++ tailWord_3608793).sum := by decide
  have hdescent : baseEnd_3608793 < baseStart_3608793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608840 : List Nat := [2, 1, 3, 2, 3, 1, 4, 1, 6]
def baseStart_3608840 : Nat := 118140960795 + 3608840 * 2 ^ 59
def prefixEnd_3608840 : Nat := 4983230072969 + 3 ^ 40 * 3608840 * 2
def baseEnd_3608840 : Nat := 205896613907973958955917

theorem tailTrace_3608840 : CollatzResearch.WordTrace tailWord_3608840 prefixEnd_3608840 205896613907973958955917 := by
  unfold tailWord_3608840
  simp only [CollatzResearch.WordTrace]
  refine ⟨65812604122898247823855987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87750138830530997098474649 65812604122898247823855987)
  ·
    refine ⟨98718906184347371735783981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65812604122898247823855987 98718906184347371735783981)
    ·
      refine ⟨37019589819130264400918993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98718906184347371735783981 37019589819130264400918993)
      ·
        refine ⟨27764692364347698300689245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37019589819130264400918993 27764692364347698300689245)
        ·
          refine ⟨10411759636630386862758467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27764692364347698300689245 10411759636630386862758467)
          ·
            refine ⟨15617639454945580294137701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10411759636630386862758467 15617639454945580294137701)
            ·
              refine ⟨2928307397802296305150819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15617639454945580294137701 2928307397802296305150819)
              ·
                refine ⟨4392461096703444457726229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2928307397802296305150819 4392461096703444457726229)
                ·
                  refine ⟨205896613907973958955917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4392461096703444457726229 205896613907973958955917)
                  ·
                    rfl

theorem cell23_3608840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4, 1, 6].length) (baseStart_3608840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3608840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3608840 prefixEnd_3608840 := by exact prefixLift 3608840
  have htrace : WordTrace (prefixWord ++ tailWord_3608840) baseStart_3608840 baseEnd_3608840 := by
    simpa [prefixWord, tailWord_3608840, baseEnd_3608840] using wordTrace_append hprefix tailTrace_3608840
  have hstable : (prefixWord ++ tailWord_3608840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608840).length < 2 ^ (prefixWord ++ tailWord_3608840).sum := by decide
  have hdescent : baseEnd_3608840 < baseStart_3608840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608867 : List Nat := [1, 1, 1, 4, 2, 2, 2, 5, 1, 1, 3]
def baseStart_3608867 : Nat := 118140960795 + 3608867 * 2 ^ 59
def prefixEnd_3608867 : Nat := 4983230072969 + 3 ^ 40 * 3608867 * 2
def baseEnd_3608867 : Nat := 1853083389149437024965629

theorem tailTrace_3608867 : CollatzResearch.WordTrace tailWord_3608867 prefixEnd_3608867 1853083389149437024965629 := by
  unfold tailWord_3608867
  simp only [CollatzResearch.WordTrace]
  refine ⟨131626193016698679258944855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87750795344465786172629903 131626193016698679258944855)
  ·
    refine ⟨197439289525048018888417283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131626193016698679258944855 197439289525048018888417283)
    ·
      refine ⟨296158934287572028332625925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197439289525048018888417283 296158934287572028332625925)
      ·
        refine ⟨55529800178919755312367361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 296158934287572028332625925 55529800178919755312367361)
        ·
          refine ⟨41647350134189816484275521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55529800178919755312367361 41647350134189816484275521)
          ·
            refine ⟨31235512600642362363206641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41647350134189816484275521 31235512600642362363206641)
            ·
              refine ⟨23426634450481771772404981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31235512600642362363206641 23426634450481771772404981)
              ·
                refine ⟨2196246979732666103662967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23426634450481771772404981 2196246979732666103662967)
                ·
                  refine ⟨3294370469598999155494451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2196246979732666103662967 3294370469598999155494451)
                  ·
                    refine ⟨4941555704398498733241677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3294370469598999155494451 4941555704398498733241677)
                    ·
                      refine ⟨1853083389149437024965629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4941555704398498733241677 1853083389149437024965629)
                      ·
                        rfl

theorem cell23_3608867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 5, 1, 1, 3].length) (baseStart_3608867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3608867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3608867 prefixEnd_3608867 := by exact prefixLift 3608867
  have htrace : WordTrace (prefixWord ++ tailWord_3608867) baseStart_3608867 baseEnd_3608867 := by
    simpa [prefixWord, tailWord_3608867, baseEnd_3608867] using wordTrace_append hprefix tailTrace_3608867
  have hstable : (prefixWord ++ tailWord_3608867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608867).length < 2 ^ (prefixWord ++ tailWord_3608867).sum := by decide
  have hdescent : baseEnd_3608867 < baseStart_3608867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608878 : List Nat := [4, 1, 3, 3, 1, 2, 2, 2, 1, 4]
def baseStart_3608878 : Nat := 118140960795 + 3608878 * 2 ^ 59
def prefixEnd_3608878 : Nat := 4983230072969 + 3 ^ 40 * 3608878 * 2
def baseEnd_3608878 : Nat := 617696345812212160642693

theorem tailTrace_3608878 : CollatzResearch.WordTrace tailWord_3608878 prefixEnd_3608878 617696345812212160642693 := by
  unfold tailWord_3608878
  simp only [CollatzResearch.WordTrace]
  refine ⟨16453324277457353517199411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87751062813105885425063525 16453324277457353517199411)
  ·
    refine ⟨24679986416186030275799117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16453324277457353517199411 24679986416186030275799117)
    ·
      refine ⟨9254994906069761353424669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24679986416186030275799117 9254994906069761353424669)
      ·
        refine ⟨3470623089776160507534251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9254994906069761353424669 3470623089776160507534251)
        ·
          refine ⟨5205934634664240761301377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3470623089776160507534251 5205934634664240761301377)
          ·
            refine ⟨3904450975998180570976033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5205934634664240761301377 3904450975998180570976033)
            ·
              refine ⟨2928338231998635428232025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3904450975998180570976033 2928338231998635428232025)
              ·
                refine ⟨2196253673998976571174019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2928338231998635428232025 2196253673998976571174019)
                ·
                  refine ⟨3294380510998464856761029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2196253673998976571174019 3294380510998464856761029)
                  ·
                    refine ⟨617696345812212160642693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3294380510998464856761029 617696345812212160642693)
                    ·
                      rfl

theorem cell23_3608878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_3608878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3608878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3608878 prefixEnd_3608878 := by exact prefixLift 3608878
  have htrace : WordTrace (prefixWord ++ tailWord_3608878) baseStart_3608878 baseEnd_3608878 := by
    simpa [prefixWord, tailWord_3608878, baseEnd_3608878] using wordTrace_append hprefix tailTrace_3608878
  have hstable : (prefixWord ++ tailWord_3608878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608878).length < 2 ^ (prefixWord ++ tailWord_3608878).sum := by decide
  have hdescent : baseEnd_3608878 < baseStart_3608878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608896 : List Nat := [2, 1, 1, 2, 2, 1, 2, 12]
def baseStart_3608896 : Nat := 118140960795 + 3608896 * 2 ^ 59
def prefixEnd_3608896 : Nat := 4983230072969 + 3 ^ 40 * 3608896 * 2
def baseEnd_3608896 : Nat := 68633269632904348574185

theorem tailTrace_3608896 : CollatzResearch.WordTrace tailWord_3608896 prefixEnd_3608896 68633269632904348574185 := by
  unfold tailWord_3608896
  simp only [CollatzResearch.WordTrace]
  refine ⟨65813625366796808605875271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87751500489062411474500361 65813625366796808605875271)
  ·
    refine ⟨98720438050195212908812907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65813625366796808605875271 98720438050195212908812907)
    ·
      refine ⟨148080657075292819363219361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98720438050195212908812907 148080657075292819363219361)
      ·
        refine ⟨111060492806469614522414521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148080657075292819363219361 111060492806469614522414521)
        ·
          refine ⟨83295369604852210891810891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111060492806469614522414521 83295369604852210891810891)
          ·
            refine ⟨124943054407278316337716337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83295369604852210891810891 124943054407278316337716337)
            ·
              refine ⟨93707290805458737253287253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124943054407278316337716337 93707290805458737253287253)
              ·
                refine ⟨68633269632904348574185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 93707290805458737253287253 68633269632904348574185)
                ·
                  rfl

theorem cell23_3608896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 12].length) (baseStart_3608896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3608896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3608896 prefixEnd_3608896 := by exact prefixLift 3608896
  have htrace : WordTrace (prefixWord ++ tailWord_3608896) baseStart_3608896 baseEnd_3608896 := by
    simpa [prefixWord, tailWord_3608896, baseEnd_3608896] using wordTrace_append hprefix tailTrace_3608896
  have hstable : (prefixWord ++ tailWord_3608896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608896).length < 2 ^ (prefixWord ++ tailWord_3608896).sum := by decide
  have hdescent : baseEnd_3608896 < baseStart_3608896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608924 : List Nat := [2, 2, 4, 3, 1, 1, 1, 3, 1, 1, 4]
def baseStart_3608924 : Nat := 118140960795 + 3608924 * 2 ^ 59
def prefixEnd_3608924 : Nat := 4983230072969 + 3 ^ 40 * 3608924 * 2
def baseEnd_3608924 : Nat := 1853112657546743301952867

theorem tailTrace_3608924 : CollatzResearch.WordTrace tailWord_3608924 prefixEnd_3608924 1853112657546743301952867 := by
  unfold tailWord_3608924
  simp only [CollatzResearch.WordTrace]
  refine ⟨65814135988746088996884913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87752181318328118662513217 65814135988746088996884913)
  ·
    refine ⟨49360601991559566747663685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65814135988746088996884913 49360601991559566747663685)
    ·
      refine ⟨9255112873417418765186941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49360601991559566747663685 9255112873417418765186941)
      ·
        refine ⟨3470667327531532036945103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9255112873417418765186941 3470667327531532036945103)
        ·
          refine ⟨5206000991297298055417655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3470667327531532036945103 5206000991297298055417655)
          ·
            refine ⟨7809001486945947083126483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5206000991297298055417655 7809001486945947083126483)
            ·
              refine ⟨11713502230418920624689725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7809001486945947083126483 11713502230418920624689725)
              ·
                refine ⟨4392563336407095234258647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11713502230418920624689725 4392563336407095234258647)
                ·
                  refine ⟨6588845004610642851387971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4392563336407095234258647 6588845004610642851387971)
                  ·
                    refine ⟨9883267506915964277081957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6588845004610642851387971 9883267506915964277081957)
                    ·
                      refine ⟨1853112657546743301952867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9883267506915964277081957 1853112657546743301952867)
                      ·
                        rfl

theorem cell23_3608924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_3608924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3608924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3608924 prefixEnd_3608924 := by exact prefixLift 3608924
  have htrace : WordTrace (prefixWord ++ tailWord_3608924) baseStart_3608924 baseEnd_3608924 := by
    simpa [prefixWord, tailWord_3608924, baseEnd_3608924] using wordTrace_append hprefix tailTrace_3608924
  have hstable : (prefixWord ++ tailWord_3608924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608924).length < 2 ^ (prefixWord ++ tailWord_3608924).sum := by decide
  have hdescent : baseEnd_3608924 < baseStart_3608924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608927 : List Nat := [1, 1, 2, 3, 1, 2, 6, 1, 1, 2, 3]
def baseStart_3608927 : Nat := 118140960795 + 3608927 * 2 ^ 59
def prefixEnd_3608927 : Nat := 4983230072969 + 3 ^ 40 * 3608927 * 2
def baseEnd_3608927 : Nat := 1853114197988706790215353

theorem tailTrace_3608927 : CollatzResearch.WordTrace tailWord_3608927 prefixEnd_3608927 1853114197988706790215353 := by
  unfold tailWord_3608927
  simp only [CollatzResearch.WordTrace]
  refine ⟨131628381396481309506129035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87752254264320873004086023 131628381396481309506129035)
  ·
    refine ⟨197442572094721964259193553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131628381396481309506129035 197442572094721964259193553)
    ·
      refine ⟨148081929071041473194395165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197442572094721964259193553 148081929071041473194395165)
      ·
        refine ⟨55530723401640552447898187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148081929071041473194395165 55530723401640552447898187)
        ·
          refine ⟨83296085102460828671847281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55530723401640552447898187 83296085102460828671847281)
          ·
            refine ⟨62472063826845621503885461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83296085102460828671847281 62472063826845621503885461)
            ·
              refine ⟨2928377991883388507994631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 62472063826845621503885461 2928377991883388507994631)
              ·
                refine ⟨4392566987825082761991947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2928377991883388507994631 4392566987825082761991947)
                ·
                  refine ⟨6588850481737624142987921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4392566987825082761991947 6588850481737624142987921)
                  ·
                    refine ⟨4941637861303218107240941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6588850481737624142987921 4941637861303218107240941)
                    ·
                      refine ⟨1853114197988706790215353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4941637861303218107240941 1853114197988706790215353)
                      ·
                        rfl

theorem cell23_3608927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6, 1, 1, 2, 3].length) (baseStart_3608927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3608927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3608927 prefixEnd_3608927 := by exact prefixLift 3608927
  have htrace : WordTrace (prefixWord ++ tailWord_3608927) baseStart_3608927 baseEnd_3608927 := by
    simpa [prefixWord, tailWord_3608927, baseEnd_3608927] using wordTrace_append hprefix tailTrace_3608927
  have hstable : (prefixWord ++ tailWord_3608927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608927).length < 2 ^ (prefixWord ++ tailWord_3608927).sum := by decide
  have hdescent : baseEnd_3608927 < baseStart_3608927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608957 : List Nat := [1, 4, 1, 1, 2, 5, 1, 1, 1, 3, 3]
def baseStart_3608957 : Nat := 118140960795 + 3608957 * 2 ^ 59
def prefixEnd_3608957 : Nat := 4983230072969 + 3 ^ 40 * 3608957 * 2
def baseEnd_3608957 : Nat := 1853129602408341672840215

theorem tailTrace_3608957 : CollatzResearch.WordTrace tailWord_3608957 prefixEnd_3608957 1853129602408341672840215 := by
  unfold tailWord_3608957
  simp only [CollatzResearch.WordTrace]
  refine ⟨131629475586372624629721125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87752983724248416419814083 131629475586372624629721125)
  ·
    refine ⟨24680526672444867118072711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131629475586372624629721125 24680526672444867118072711)
    ·
      refine ⟨37020790008667300677109067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24680526672444867118072711 37020790008667300677109067)
      ·
        refine ⟨55531185013000951015663601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37020790008667300677109067 55531185013000951015663601)
        ·
          refine ⟨41648388759750713261747701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55531185013000951015663601 41648388759750713261747701)
          ·
            refine ⟨3904536446226629368288847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41648388759750713261747701 3904536446226629368288847)
            ·
              refine ⟨5856804669339944052433271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3904536446226629368288847 5856804669339944052433271)
              ·
                refine ⟨8785207004009916078649907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5856804669339944052433271 8785207004009916078649907)
                ·
                  refine ⟨13177810506014874117974861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8785207004009916078649907 13177810506014874117974861)
                  ·
                    refine ⟨4941678939755577794240573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13177810506014874117974861 4941678939755577794240573)
                    ·
                      refine ⟨1853129602408341672840215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4941678939755577794240573 1853129602408341672840215)
                      ·
                        rfl

theorem cell23_3608957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 1, 1, 3, 3].length) (baseStart_3608957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3608957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3608957 prefixEnd_3608957 := by exact prefixLift 3608957
  have htrace : WordTrace (prefixWord ++ tailWord_3608957) baseStart_3608957 baseEnd_3608957 := by
    simpa [prefixWord, tailWord_3608957, baseEnd_3608957] using wordTrace_append hprefix tailTrace_3608957
  have hstable : (prefixWord ++ tailWord_3608957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608957).length < 2 ^ (prefixWord ++ tailWord_3608957).sum := by decide
  have hdescent : baseEnd_3608957 < baseStart_3608957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608983 : List Nat := [1, 1, 3, 3, 1, 1, 3, 1, 1, 3, 5]
def baseStart_3608983 : Nat := 118140960795 + 3608983 * 2 ^ 59
def prefixEnd_3608983 : Nat := 4983230072969 + 3 ^ 40 * 3608983 * 2
def baseEnd_3608983 : Nat := 1853142952905358571115095

theorem tailTrace_3608983 : CollatzResearch.WordTrace tailWord_3608983 prefixEnd_3608983 1853142952905358571115095 := by
  unfold tailWord_3608983
  simp only [CollatzResearch.WordTrace]
  refine ⟨131630423884278431070167603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87753615922852287380111735 131630423884278431070167603)
  ·
    refine ⟨197445635826417646605251405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131630423884278431070167603 197445635826417646605251405)
    ·
      refine ⟨74042113434906617476969277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197445635826417646605251405 74042113434906617476969277)
      ·
        refine ⟨27765792538089981553863479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74042113434906617476969277 27765792538089981553863479)
        ·
          refine ⟨41648688807134972330795219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27765792538089981553863479 41648688807134972330795219)
          ·
            refine ⟨62473033210702458496192829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41648688807134972330795219 62473033210702458496192829)
            ·
              refine ⟨23427387454013421936072311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62473033210702458496192829 23427387454013421936072311)
              ·
                refine ⟨35141081181020132904108467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23427387454013421936072311 35141081181020132904108467)
                ·
                  refine ⟨52711621771530199356162701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35141081181020132904108467 52711621771530199356162701)
                  ·
                    refine ⟨19766858164323824758561013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52711621771530199356162701 19766858164323824758561013)
                    ·
                      refine ⟨1853142952905358571115095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19766858164323824758561013 1853142952905358571115095)
                      ·
                        rfl

theorem cell23_3608983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_3608983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3608983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3608983 prefixEnd_3608983 := by exact prefixLift 3608983
  have htrace : WordTrace (prefixWord ++ tailWord_3608983) baseStart_3608983 baseEnd_3608983 := by
    simpa [prefixWord, tailWord_3608983, baseEnd_3608983] using wordTrace_append hprefix tailTrace_3608983
  have hstable : (prefixWord ++ tailWord_3608983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608983).length < 2 ^ (prefixWord ++ tailWord_3608983).sum := by decide
  have hdescent : baseEnd_3608983 < baseStart_3608983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608984 : List Nat := [2, 1, 2, 5, 1, 1, 2, 3, 1, 3, 2]
def baseStart_3608984 : Nat := 118140960795 + 3608984 * 2 ^ 59
def prefixEnd_3608984 : Nat := 4983230072969 + 3 ^ 40 * 3608984 * 2
def baseEnd_3608984 : Nat := 1853143466386013067202591

theorem tailTrace_3608984 : CollatzResearch.WordTrace tailWord_3608984 prefixEnd_3608984 1853143466386013067202591 := by
  unfold tailWord_3608984
  simp only [CollatzResearch.WordTrace]
  refine ⟨65815230178637404120477003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87753640238183205493969337 65815230178637404120477003)
  ·
    refine ⟨98722845267956106180715505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65815230178637404120477003 98722845267956106180715505)
    ·
      refine ⟨74042133950967079635536629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98722845267956106180715505 74042133950967079635536629)
      ·
        refine ⟨6941450057903163715831559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74042133950967079635536629 6941450057903163715831559)
        ·
          refine ⟨10412175086854745573747339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6941450057903163715831559 10412175086854745573747339)
          ·
            refine ⟨15618262630282118360621009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10412175086854745573747339 15618262630282118360621009)
            ·
              refine ⟨11713696972711588770465757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15618262630282118360621009 11713696972711588770465757)
              ·
                refine ⟨4392636364766845788924659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11713696972711588770465757 4392636364766845788924659)
                ·
                  refine ⟨6588954547150268683386989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4392636364766845788924659 6588954547150268683386989)
                  ·
                    refine ⟨2470857955181350756270121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6588954547150268683386989 2470857955181350756270121)
                    ·
                      refine ⟨1853143466386013067202591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2470857955181350756270121 1853143466386013067202591)
                      ·
                        rfl

theorem cell23_3608984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_3608984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3608984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3608984 prefixEnd_3608984 := by exact prefixLift 3608984
  have htrace : WordTrace (prefixWord ++ tailWord_3608984) baseStart_3608984 baseEnd_3608984 := by
    simpa [prefixWord, tailWord_3608984, baseEnd_3608984] using wordTrace_append hprefix tailTrace_3608984
  have hstable : (prefixWord ++ tailWord_3608984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608984).length < 2 ^ (prefixWord ++ tailWord_3608984).sum := by decide
  have hdescent : baseEnd_3608984 < baseStart_3608984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3608997 : List Nat := [1, 3, 1, 2, 1, 1, 3, 3, 4, 2, 2]
def baseStart_3608997 : Nat := 118140960795 + 3608997 * 2 ^ 59
def prefixEnd_3608997 : Nat := 4983230072969 + 3 ^ 40 * 3608997 * 2
def baseEnd_3608997 : Nat := 1853150141634521516340031

theorem tailTrace_3608997 : CollatzResearch.WordTrace tailWord_3608997 prefixEnd_3608997 1853150141634521516340031 := by
  unfold tailWord_3608997
  simp only [CollatzResearch.WordTrace]
  refine ⟨131630934506227711461177245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87753956337485140974118163 131630934506227711461177245)
  ·
    refine ⟨49361600439835391797941467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131630934506227711461177245 49361600439835391797941467)
    ·
      refine ⟨74042400659753087696912201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49361600439835391797941467 74042400659753087696912201)
      ·
        refine ⟨55531800494814815772684151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74042400659753087696912201 55531800494814815772684151)
        ·
          refine ⟨83297700742222223659026227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55531800494814815772684151 83297700742222223659026227)
          ·
            refine ⟨124946551113333335488539341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83297700742222223659026227 124946551113333335488539341)
            ·
              refine ⟨46854956667500000808202253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124946551113333335488539341 46854956667500000808202253)
              ·
                refine ⟨17570608750312500303075845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46854956667500000808202253 17570608750312500303075845)
                ·
                  refine ⟨3294489140683593806826721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17570608750312500303075845 3294489140683593806826721)
                  ·
                    refine ⟨2470866855512695355120041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3294489140683593806826721 2470866855512695355120041)
                    ·
                      refine ⟨1853150141634521516340031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2470866855512695355120041 1853150141634521516340031)
                      ·
                        rfl

theorem cell23_3608997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 4, 2, 2].length) (baseStart_3608997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3608997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3608997 prefixEnd_3608997 := by exact prefixLift 3608997
  have htrace : WordTrace (prefixWord ++ tailWord_3608997) baseStart_3608997 baseEnd_3608997 := by
    simpa [prefixWord, tailWord_3608997, baseEnd_3608997] using wordTrace_append hprefix tailTrace_3608997
  have hstable : (prefixWord ++ tailWord_3608997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3608997).length < 2 ^ (prefixWord ++ tailWord_3608997).sum := by decide
  have hdescent : baseEnd_3608997 < baseStart_3608997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3608997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609033 : List Nat := [1, 2, 1, 1, 2, 1, 4, 3, 1, 7]
def baseStart_3609033 : Nat := 118140960795 + 3609033 * 2 ^ 59
def prefixEnd_3609033 : Nat := 4983230072969 + 3 ^ 40 * 3609033 * 2
def baseEnd_3609033 : Nat := 617722875646027791829955

theorem tailTrace_3609033 : CollatzResearch.WordTrace tailWord_3609033 prefixEnd_3609033 617722875646027791829955 := by
  unfold tailWord_3609033
  simp only [CollatzResearch.WordTrace]
  refine ⟨131632247534097289609487753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87754831689398193072991835 131632247534097289609487753)
  ·
    refine ⟨98724185650572967207115815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131632247534097289609487753 98724185650572967207115815)
    ·
      refine ⟨148086278475859450810673723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98724185650572967207115815 148086278475859450810673723)
      ·
        refine ⟨222129417713789176216010585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148086278475859450810673723 222129417713789176216010585)
        ·
          refine ⟨166597063285341882162007939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222129417713789176216010585 166597063285341882162007939)
          ·
            refine ⟨249895594928012823243011909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166597063285341882162007939 249895594928012823243011909)
            ·
              refine ⟨46855424049002404358064733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 249895594928012823243011909 46855424049002404358064733)
              ·
                refine ⟨17570784018375901634274275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46855424049002404358064733 17570784018375901634274275)
                ·
                  refine ⟨26356176027563852451411413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17570784018375901634274275 26356176027563852451411413)
                  ·
                    refine ⟨617722875646027791829955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26356176027563852451411413 617722875646027791829955)
                    ·
                      rfl

theorem cell23_3609033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 7].length) (baseStart_3609033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3609033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3609033 prefixEnd_3609033 := by exact prefixLift 3609033
  have htrace : WordTrace (prefixWord ++ tailWord_3609033) baseStart_3609033 baseEnd_3609033 := by
    simpa [prefixWord, tailWord_3609033, baseEnd_3609033] using wordTrace_append hprefix tailTrace_3609033
  have hstable : (prefixWord ++ tailWord_3609033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609033).length < 2 ^ (prefixWord ++ tailWord_3609033).sum := by decide
  have hdescent : baseEnd_3609033 < baseStart_3609033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609040 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 3, 7, 2]
def baseStart_3609040 : Nat := 118140960795 + 3609040 * 2 ^ 59
def prefixEnd_3609040 : Nat := 4983230072969 + 3 ^ 40 * 3609040 * 2
def baseEnd_3609040 : Nat := 1853172221302664848102333

theorem tailTrace_3609040 : CollatzResearch.WordTrace tailWord_3609040 prefixEnd_3609040 1853172221302664848102333 := by
  unfold tailWord_3609040
  simp only [CollatzResearch.WordTrace]
  refine ⟨65816251422535964902496287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87755001896714619869995049 65816251422535964902496287)
  ·
    refine ⟨98724377133803947353744431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65816251422535964902496287 98724377133803947353744431)
    ·
      refine ⟨148086565700705921030616647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98724377133803947353744431 148086565700705921030616647)
      ·
        refine ⟨222129848551058881545924971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148086565700705921030616647 222129848551058881545924971)
        ·
          refine ⟨333194772826588322318887457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222129848551058881545924971 333194772826588322318887457)
          ·
            refine ⟨249896079619941241739165593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 333194772826588322318887457 249896079619941241739165593)
            ·
              refine ⟨187422059714955931304374195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 249896079619941241739165593 187422059714955931304374195)
              ·
                refine ⟨281133089572433896956561293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187422059714955931304374195 281133089572433896956561293)
                ·
                  refine ⟨105424908589662711358710485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 281133089572433896956561293 105424908589662711358710485)
                  ·
                    refine ⟨2470896295070219797469777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 105424908589662711358710485 2470896295070219797469777)
                    ·
                      refine ⟨1853172221302664848102333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2470896295070219797469777 1853172221302664848102333)
                      ·
                        rfl

theorem cell23_3609040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 3, 7, 2].length) (baseStart_3609040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3609040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3609040 prefixEnd_3609040 := by exact prefixLift 3609040
  have htrace : WordTrace (prefixWord ++ tailWord_3609040) baseStart_3609040 baseEnd_3609040 := by
    simpa [prefixWord, tailWord_3609040, baseEnd_3609040] using wordTrace_append hprefix tailTrace_3609040
  have hstable : (prefixWord ++ tailWord_3609040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609040).length < 2 ^ (prefixWord ++ tailWord_3609040).sum := by decide
  have hdescent : baseEnd_3609040 < baseStart_3609040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609050 : List Nat := [3, 1, 1, 2, 3, 1, 1, 4, 2, 5]
def baseStart_3609050 : Nat := 118140960795 + 3609050 * 2 ^ 59
def prefixEnd_3609050 : Nat := 4983230072969 + 3 ^ 40 * 3609050 * 2
def baseEnd_3609050 : Nat := 617725785369736602992429

theorem tailTrace_3609050 : CollatzResearch.WordTrace tailWord_3609050 prefixEnd_3609050 617725785369736602992429 := by
  unfold tailWord_3609050
  simp only [CollatzResearch.WordTrace]
  refine ⟨32908216893758925378214151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87755245050023801008571069 32908216893758925378214151)
  ·
    refine ⟨49362325340638388067321227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32908216893758925378214151 49362325340638388067321227)
    ·
      refine ⟨74043488010957582100981841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49362325340638388067321227 74043488010957582100981841)
      ·
        refine ⟨55532616008218186575736381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74043488010957582100981841 55532616008218186575736381)
        ·
          refine ⟨20824731003081819965901143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55532616008218186575736381 20824731003081819965901143)
          ·
            refine ⟨31237096504622729948851715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20824731003081819965901143 31237096504622729948851715)
            ·
              refine ⟨46855644756934094923277573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31237096504622729948851715 46855644756934094923277573)
              ·
                refine ⟨8785433391925142798114545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46855644756934094923277573 8785433391925142798114545)
                ·
                  refine ⟨6589075043943857098585909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8785433391925142798114545 6589075043943857098585909)
                  ·
                    refine ⟨617725785369736602992429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6589075043943857098585909 617725785369736602992429)
                    ·
                      rfl

theorem cell23_3609050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 4, 2, 5].length) (baseStart_3609050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3609050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3609050 prefixEnd_3609050 := by exact prefixLift 3609050
  have htrace : WordTrace (prefixWord ++ tailWord_3609050) baseStart_3609050 baseEnd_3609050 := by
    simpa [prefixWord, tailWord_3609050, baseEnd_3609050] using wordTrace_append hprefix tailTrace_3609050
  have hstable : (prefixWord ++ tailWord_3609050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609050).length < 2 ^ (prefixWord ++ tailWord_3609050).sum := by decide
  have hdescent : baseEnd_3609050 < baseStart_3609050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609083 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 6]
def baseStart_3609083 : Nat := 118140960795 + 3609083 * 2 ^ 59
def prefixEnd_3609083 : Nat := 4983230072969 + 3 ^ 40 * 3609083 * 2
def baseEnd_3609083 : Nat := 1853194300970808179864635

theorem tailTrace_3609083 : CollatzResearch.WordTrace tailWord_3609083 prefixEnd_3609083 1853194300970808179864635 := by
  unfold tailWord_3609083
  simp only [CollatzResearch.WordTrace]
  refine ⟨131634071183916148148807903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87756047455944098765871935 131634071183916148148807903)
  ·
    refine ⟨197451106775874222223211855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131634071183916148148807903 197451106775874222223211855)
    ·
      refine ⟨296176660163811333334817783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197451106775874222223211855 296176660163811333334817783)
      ·
        refine ⟨444264990245717000002226675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296176660163811333334817783 444264990245717000002226675)
        ·
          refine ⟨666397485368575500003340013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444264990245717000002226675 666397485368575500003340013)
          ·
            refine ⟨249899057013215812501252505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 666397485368575500003340013 249899057013215812501252505)
            ·
              refine ⟨187424292759911859375939379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 249899057013215812501252505 187424292759911859375939379)
              ·
                refine ⟨281136439139867789063909069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187424292759911859375939379 281136439139867789063909069)
                ·
                  refine ⟨105426164677450420898965901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 281136439139867789063909069 105426164677450420898965901)
                  ·
                    refine ⟨39534811754043907837112213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 105426164677450420898965901 39534811754043907837112213)
                    ·
                      refine ⟨1853194300970808179864635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39534811754043907837112213 1853194300970808179864635)
                      ·
                        rfl

theorem cell23_3609083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 6].length) (baseStart_3609083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3609083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3609083 prefixEnd_3609083 := by exact prefixLift 3609083
  have htrace : WordTrace (prefixWord ++ tailWord_3609083) baseStart_3609083 baseEnd_3609083 := by
    simpa [prefixWord, tailWord_3609083, baseEnd_3609083] using wordTrace_append hprefix tailTrace_3609083
  have hstable : (prefixWord ++ tailWord_3609083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609083).length < 2 ^ (prefixWord ++ tailWord_3609083).sum := by decide
  have hdescent : baseEnd_3609083 < baseStart_3609083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609100 : List Nat := [2, 2, 1, 2, 4, 1, 1, 1, 2, 1, 6]
def baseStart_3609100 : Nat := 118140960795 + 3609100 * 2 ^ 59
def prefixEnd_3609100 : Nat := 4983230072969 + 3 ^ 40 * 3609100 * 2
def baseEnd_3609100 : Nat := 1853203030141934613352057

theorem tailTrace_3609100 : CollatzResearch.WordTrace tailWord_3609100 prefixEnd_3609100 1853203030141934613352057 := by
  unfold tailWord_3609100
  simp only [CollatzResearch.WordTrace]
  refine ⟨65817345612427280026088377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87756460816569706701451169 65817345612427280026088377)
  ·
    refine ⟨49363009209320460019566283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65817345612427280026088377 49363009209320460019566283)
    ·
      refine ⟨74044513813980690029349425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49363009209320460019566283 74044513813980690029349425)
      ·
        refine ⟨55533385360485517522012069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74044513813980690029349425 55533385360485517522012069)
        ·
          refine ⟨10412509755091034535377263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55533385360485517522012069 10412509755091034535377263)
          ·
            refine ⟨15618764632636551803065895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10412509755091034535377263 15618764632636551803065895)
            ·
              refine ⟨23428146948954827704598843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15618764632636551803065895 23428146948954827704598843)
              ·
                refine ⟨35142220423432241556898265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23428146948954827704598843 35142220423432241556898265)
                ·
                  refine ⟨26356665317574181167673699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35142220423432241556898265 26356665317574181167673699)
                  ·
                    refine ⟨39534997976361271751510549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26356665317574181167673699 39534997976361271751510549)
                    ·
                      refine ⟨1853203030141934613352057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39534997976361271751510549 1853203030141934613352057)
                      ·
                        rfl

theorem cell23_3609100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_3609100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3609100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3609100 prefixEnd_3609100 := by exact prefixLift 3609100
  have htrace : WordTrace (prefixWord ++ tailWord_3609100) baseStart_3609100 baseEnd_3609100 := by
    simpa [prefixWord, tailWord_3609100, baseEnd_3609100] using wordTrace_append hprefix tailTrace_3609100
  have hstable : (prefixWord ++ tailWord_3609100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609100).length < 2 ^ (prefixWord ++ tailWord_3609100).sum := by decide
  have hdescent : baseEnd_3609100 < baseStart_3609100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609114 : List Nat := [3, 1, 1, 3, 1, 1, 4, 4, 1, 4]
def baseStart_3609114 : Nat := 118140960795 + 3609114 * 2 ^ 59
def prefixEnd_3609114 : Nat := 4983230072969 + 3 ^ 40 * 3609114 * 2
def baseEnd_3609114 : Nat := 617736739623699186192331

theorem tailTrace_3609114 : CollatzResearch.WordTrace tailWord_3609114 prefixEnd_3609114 617736739623699186192331 := by
  unfold tailWord_3609114
  simp only [CollatzResearch.WordTrace]
  refine ⟨32908800461700960110796599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87756801231202560295457597 32908800461700960110796599)
  ·
    refine ⟨49363200692551440166194899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32908800461700960110796599 49363200692551440166194899)
    ·
      refine ⟨74044801038827160249292349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49363200692551440166194899 74044801038827160249292349)
      ·
        refine ⟨27766800389560185093484631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74044801038827160249292349 27766800389560185093484631)
        ·
          refine ⟨41650200584340277640226947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27766800389560185093484631 41650200584340277640226947)
          ·
            refine ⟨62475300876510416460340421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41650200584340277640226947 62475300876510416460340421)
            ·
              refine ⟨11714118914345703086313829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62475300876510416460340421 11714118914345703086313829)
              ·
                refine ⟨2196397296439819328683843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11714118914345703086313829 2196397296439819328683843)
                ·
                  refine ⟨3294595944659728993025765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2196397296439819328683843 3294595944659728993025765)
                  ·
                    refine ⟨617736739623699186192331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3294595944659728993025765 617736739623699186192331)
                    ·
                      rfl

theorem cell23_3609114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 4, 1, 4].length) (baseStart_3609114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3609114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3609114 prefixEnd_3609114 := by exact prefixLift 3609114
  have htrace : WordTrace (prefixWord ++ tailWord_3609114) baseStart_3609114 baseEnd_3609114 := by
    simpa [prefixWord, tailWord_3609114, baseEnd_3609114] using wordTrace_append hprefix tailTrace_3609114
  have hstable : (prefixWord ++ tailWord_3609114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609114).length < 2 ^ (prefixWord ++ tailWord_3609114).sum := by decide
  have hdescent : baseEnd_3609114 < baseStart_3609114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609157 : List Nat := [1, 3, 1, 1, 1, 5, 2, 3, 1, 5]
def baseStart_3609157 : Nat := 118140960795 + 3609157 * 2 ^ 59
def prefixEnd_3609157 : Nat := 4983230072969 + 3 ^ 40 * 3609157 * 2
def baseEnd_3609157 : Nat := 617744099513080296779765

theorem tailTrace_3609157 : CollatzResearch.WordTrace tailWord_3609157 prefixEnd_3609157 617744099513080296779765 := by
  unfold tailWord_3609157
  simp only [CollatzResearch.WordTrace]
  refine ⟨131636770185648058787001725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87757846790432039191334483 131636770185648058787001725)
  ·
    refine ⟨49363788819618022045125647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131636770185648058787001725 49363788819618022045125647)
    ·
      refine ⟨74045683229427033067688471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49363788819618022045125647 74045683229427033067688471)
      ·
        refine ⟨111068524844140549601532707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74045683229427033067688471 111068524844140549601532707)
        ·
          refine ⟨166602787266210824402299061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111068524844140549601532707 166602787266210824402299061)
          ·
            refine ⟨15619011306207264787715537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 166602787266210824402299061 15619011306207264787715537)
            ·
              refine ⟨11714258479655448590786653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15619011306207264787715537 11714258479655448590786653)
              ·
                refine ⟨4392846929870793221544995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11714258479655448590786653 4392846929870793221544995)
                ·
                  refine ⟨6589270394806189832317493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4392846929870793221544995 6589270394806189832317493)
                  ·
                    refine ⟨617744099513080296779765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6589270394806189832317493 617744099513080296779765)
                    ·
                      rfl

theorem cell23_3609157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 3, 1, 5].length) (baseStart_3609157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3609157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3609157 prefixEnd_3609157 := by exact prefixLift 3609157
  have htrace : WordTrace (prefixWord ++ tailWord_3609157) baseStart_3609157 baseEnd_3609157 := by
    simpa [prefixWord, tailWord_3609157, baseEnd_3609157] using wordTrace_append hprefix tailTrace_3609157
  have hstable : (prefixWord ++ tailWord_3609157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609157).length < 2 ^ (prefixWord ++ tailWord_3609157).sum := by decide
  have hdescent : baseEnd_3609157 < baseStart_3609157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609164 : List Nat := [2, 2, 1, 3, 1, 2, 3, 2, 2, 3, 2]
def baseStart_3609164 : Nat := 118140960795 + 3609164 * 2 ^ 59
def prefixEnd_3609164 : Nat := 4983230072969 + 3 ^ 40 * 3609164 * 2
def baseEnd_3609164 : Nat := 1853235892903822362951763

theorem tailTrace_3609164 : CollatzResearch.WordTrace tailWord_3609164 prefixEnd_3609164 1853235892903822362951763 := by
  unfold tailWord_3609164
  simp only [CollatzResearch.WordTrace]
  refine ⟨65818512748311349491253273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87758016997748465988337697 65818512748311349491253273)
  ·
    refine ⟨49363884561233512118439955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65818512748311349491253273 49363884561233512118439955)
    ·
      refine ⟨74045826841850268177659933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49363884561233512118439955 74045826841850268177659933)
      ·
        refine ⟨27767185065693850566622475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74045826841850268177659933 27767185065693850566622475)
        ·
          refine ⟨41650777598540775849933713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27767185065693850566622475 41650777598540775849933713)
          ·
            refine ⟨31238083198905581887450285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41650777598540775849933713 31238083198905581887450285)
            ·
              refine ⟨11714281199589593207793857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31238083198905581887450285 11714281199589593207793857)
              ·
                refine ⟨8785710899692194905845393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11714281199589593207793857 8785710899692194905845393)
                ·
                  refine ⟨6589283174769146179384045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8785710899692194905845393 6589283174769146179384045)
                  ·
                    refine ⟨2470981190538429817269017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6589283174769146179384045 2470981190538429817269017)
                    ·
                      refine ⟨1853235892903822362951763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2470981190538429817269017 1853235892903822362951763)
                      ·
                        rfl

theorem cell23_3609164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 2, 2, 3, 2].length) (baseStart_3609164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3609164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3609164 prefixEnd_3609164 := by exact prefixLift 3609164
  have htrace : WordTrace (prefixWord ++ tailWord_3609164) baseStart_3609164 baseEnd_3609164 := by
    simpa [prefixWord, tailWord_3609164, baseEnd_3609164] using wordTrace_append hprefix tailTrace_3609164
  have hstable : (prefixWord ++ tailWord_3609164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609164).length < 2 ^ (prefixWord ++ tailWord_3609164).sum := by decide
  have hdescent : baseEnd_3609164 < baseStart_3609164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609234 : List Nat := [3, 2, 3, 1, 2, 3, 1, 8]
def baseStart_3609234 : Nat := 118140960795 + 3609234 * 2 ^ 59
def prefixEnd_3609234 : Nat := 4983230072969 + 3 ^ 40 * 3609234 * 2
def baseEnd_3609234 : Nat := 68639697649986558854683

theorem tailTrace_3609234 : CollatzResearch.WordTrace tailWord_3609234 prefixEnd_3609234 68639697649986558854683 := by
  unfold tailWord_3609234
  simp only [CollatzResearch.WordTrace]
  refine ⟨32909894651592275234388689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87759719070912733958369837 32909894651592275234388689)
  ·
    refine ⟨24682420988694206425791517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32909894651592275234388689 24682420988694206425791517)
    ·
      refine ⟨9255907870760327409671819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24682420988694206425791517 9255907870760327409671819)
      ·
        refine ⟨13883861806140491114507729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9255907870760327409671819 13883861806140491114507729)
        ·
          refine ⟨10412896354605368335880797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13883861806140491114507729 10412896354605368335880797)
          ·
            refine ⟨3904836132977013125955299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10412896354605368335880797 3904836132977013125955299)
            ·
              refine ⟨5857254199465519688932949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3904836132977013125955299 5857254199465519688932949)
              ·
                refine ⟨68639697649986558854683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5857254199465519688932949 68639697649986558854683)
                ·
                  rfl

theorem cell23_3609234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 8].length) (baseStart_3609234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3609234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3609234 prefixEnd_3609234 := by exact prefixLift 3609234
  have htrace : WordTrace (prefixWord ++ tailWord_3609234) baseStart_3609234 baseEnd_3609234 := by
    simpa [prefixWord, tailWord_3609234, baseEnd_3609234] using wordTrace_append hprefix tailTrace_3609234
  have hstable : (prefixWord ++ tailWord_3609234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609234).length < 2 ^ (prefixWord ++ tailWord_3609234).sum := by decide
  have hdescent : baseEnd_3609234 < baseStart_3609234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609244 : List Nat := [2, 2, 3, 2, 2, 1, 1, 3, 1, 3, 3]
def baseStart_3609244 : Nat := 118140960795 + 3609244 * 2 ^ 59
def prefixEnd_3609244 : Nat := 4983230072969 + 3 ^ 40 * 3609244 * 2
def baseEnd_3609244 : Nat := 1853276971356182049951395

theorem tailTrace_3609244 : CollatzResearch.WordTrace tailWord_3609244 prefixEnd_3609244 1853276971356182049951395 := by
  unfold tailWord_3609244
  simp only [CollatzResearch.WordTrace]
  refine ⟨65819971668166436322709393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87759962224221915096945857 65819971668166436322709393)
  ·
    refine ⟨49364978751124827242032045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65819971668166436322709393 49364978751124827242032045)
    ·
      refine ⟨18511867031671810215762017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49364978751124827242032045 18511867031671810215762017)
      ·
        refine ⟨13883900273753857661821513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18511867031671810215762017 13883900273753857661821513)
        ·
          refine ⟨10412925205315393246366135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13883900273753857661821513 10412925205315393246366135)
          ·
            refine ⟨15619387807973089869549203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10412925205315393246366135 15619387807973089869549203)
            ·
              refine ⟨23429081711959634804323805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15619387807973089869549203 23429081711959634804323805)
              ·
                refine ⟨8785905641984863051621427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23429081711959634804323805 8785905641984863051621427)
                ·
                  refine ⟨13178858462977294577432141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8785905641984863051621427 13178858462977294577432141)
                  ·
                    refine ⟨4942071923616485466537053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13178858462977294577432141 4942071923616485466537053)
                    ·
                      refine ⟨1853276971356182049951395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4942071923616485466537053 1853276971356182049951395)
                      ·
                        rfl

theorem cell23_3609244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_3609244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3609244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3609244 prefixEnd_3609244 := by exact prefixLift 3609244
  have htrace : WordTrace (prefixWord ++ tailWord_3609244) baseStart_3609244 baseEnd_3609244 := by
    simpa [prefixWord, tailWord_3609244, baseEnd_3609244] using wordTrace_append hprefix tailTrace_3609244
  have hstable : (prefixWord ++ tailWord_3609244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609244).length < 2 ^ (prefixWord ++ tailWord_3609244).sum := by decide
  have hdescent : baseEnd_3609244 < baseStart_3609244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609262 : List Nat := [4, 1, 4, 1, 1, 2, 2, 3, 1, 2, 2]
def baseStart_3609262 : Nat := 118140960795 + 3609262 * 2 ^ 59
def prefixEnd_3609262 : Nat := 4983230072969 + 3 ^ 40 * 3609262 * 2
def baseEnd_3609262 : Nat := 1853286214007962979526313

theorem tailTrace_3609262 : CollatzResearch.WordTrace tailWord_3609262 prefixEnd_3609262 1853286214007962979526313 := by
  unfold tailWord_3609262
  simp only [CollatzResearch.WordTrace]
  refine ⟨16455074981283457714946755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87760399900178441146382693 16455074981283457714946755)
  ·
    refine ⟨24682612471925186572420133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16455074981283457714946755 24682612471925186572420133)
    ·
      refine ⟨4627989838485972482328775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24682612471925186572420133 4627989838485972482328775)
      ·
        refine ⟨6941984757728958723493163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4627989838485972482328775 6941984757728958723493163)
        ·
          refine ⟨10412977136593438085239745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6941984757728958723493163 10412977136593438085239745)
          ·
            refine ⟨7809732852445078563929809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10412977136593438085239745 7809732852445078563929809)
            ·
              refine ⟨5857299639333808922947357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7809732852445078563929809 5857299639333808922947357)
              ·
                refine ⟨2196487364750178346105259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5857299639333808922947357 2196487364750178346105259)
                ·
                  refine ⟨3294731047125267519157889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2196487364750178346105259 3294731047125267519157889)
                  ·
                    refine ⟨2471048285343950639368417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3294731047125267519157889 2471048285343950639368417)
                    ·
                      refine ⟨1853286214007962979526313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2471048285343950639368417 1853286214007962979526313)
                      ·
                        rfl

theorem cell23_3609262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_3609262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3609262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3609262 prefixEnd_3609262 := by exact prefixLift 3609262
  have htrace : WordTrace (prefixWord ++ tailWord_3609262) baseStart_3609262 baseEnd_3609262 := by
    simpa [prefixWord, tailWord_3609262, baseEnd_3609262] using wordTrace_append hprefix tailTrace_3609262
  have hstable : (prefixWord ++ tailWord_3609262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609262).length < 2 ^ (prefixWord ++ tailWord_3609262).sum := by decide
  have hdescent : baseEnd_3609262 < baseStart_3609262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609265 : List Nat := [1, 2, 2, 6, 1, 2, 2, 1, 1, 2, 3]
def baseStart_3609265 : Nat := 118140960795 + 3609265 * 2 ^ 59
def prefixEnd_3609265 : Nat := 4983230072969 + 3 ^ 40 * 3609265 * 2
def baseEnd_3609265 : Nat := 1853287754449926467788799

theorem tailTrace_3609265 : CollatzResearch.WordTrace tailWord_3609265 prefixEnd_3609265 1853287754449926467788799 := by
  unfold tailWord_3609265
  simp only [CollatzResearch.WordTrace]
  refine ⟨131640709269256793231933249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87760472846171195487955499 131640709269256793231933249)
  ·
    refine ⟨98730531951942594923949937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131640709269256793231933249 98730531951942594923949937)
    ·
      refine ⟨74047898963956946192962453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98730531951942594923949937 74047898963956946192962453)
      ·
        refine ⟨3470995263935481852795115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 74047898963956946192962453 3470995263935481852795115)
        ·
          refine ⟨5206492895903222779192673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3470995263935481852795115 5206492895903222779192673)
          ·
            refine ⟨3904869671927417084394505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5206492895903222779192673 3904869671927417084394505)
            ·
              refine ⟨2928652253945562813295879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3904869671927417084394505 2928652253945562813295879)
              ·
                refine ⟨4392978380918344219943819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2928652253945562813295879 4392978380918344219943819)
                ·
                  refine ⟨6589467571377516329915729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4392978380918344219943819 6589467571377516329915729)
                  ·
                    refine ⟨4942100678533137247436797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6589467571377516329915729 4942100678533137247436797)
                    ·
                      refine ⟨1853287754449926467788799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4942100678533137247436797 1853287754449926467788799)
                      ·
                        rfl

theorem cell23_3609265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_3609265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3609265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3609265 prefixEnd_3609265 := by exact prefixLift 3609265
  have htrace : WordTrace (prefixWord ++ tailWord_3609265) baseStart_3609265 baseEnd_3609265 := by
    simpa [prefixWord, tailWord_3609265, baseEnd_3609265] using wordTrace_append hprefix tailTrace_3609265
  have hstable : (prefixWord ++ tailWord_3609265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609265).length < 2 ^ (prefixWord ++ tailWord_3609265).sum := by decide
  have hdescent : baseEnd_3609265 < baseStart_3609265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609277 : List Nat := [1, 4, 1, 2, 1, 3, 1, 2, 2, 6]
def baseStart_3609277 : Nat := 118140960795 + 3609277 * 2 ^ 59
def prefixEnd_3609277 : Nat := 4983230072969 + 3 ^ 40 * 3609277 * 2
def baseEnd_3609277 : Nat := 617764638739260140279581

theorem tailTrace_3609277 : CollatzResearch.WordTrace tailWord_3609277 prefixEnd_3609277 617764638739260140279581 := by
  unfold tailWord_3609277
  simp only [CollatzResearch.WordTrace]
  refine ⟨131641146945213319281370085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87760764630142212854246723 131641146945213319281370085)
  ·
    refine ⟨24682715052227497365256891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131641146945213319281370085 24682715052227497365256891)
    ·
      refine ⟨37024072578341246047885337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24682715052227497365256891 37024072578341246047885337)
      ·
        refine ⟨27768054433755934535914003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37024072578341246047885337 27768054433755934535914003)
        ·
          refine ⟨41652081650633901803871005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27768054433755934535914003 41652081650633901803871005)
          ·
            refine ⟨15619530618987713176451627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41652081650633901803871005 15619530618987713176451627)
            ·
              refine ⟨23429295928481569764677441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15619530618987713176451627 23429295928481569764677441)
              ·
                refine ⟨17571971946361177323508081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23429295928481569764677441 17571971946361177323508081)
                ·
                  refine ⟨13178978959770882992631061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17571971946361177323508081 13178978959770882992631061)
                  ·
                    refine ⟨617764638739260140279581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13178978959770882992631061 617764638739260140279581)
                    ·
                      rfl

theorem cell23_3609277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 2, 6].length) (baseStart_3609277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3609277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3609277 prefixEnd_3609277 := by exact prefixLift 3609277
  have htrace : WordTrace (prefixWord ++ tailWord_3609277) baseStart_3609277 baseEnd_3609277 := by
    simpa [prefixWord, tailWord_3609277, baseEnd_3609277] using wordTrace_append hprefix tailTrace_3609277
  have hstable : (prefixWord ++ tailWord_3609277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609277).length < 2 ^ (prefixWord ++ tailWord_3609277).sum := by decide
  have hdescent : baseEnd_3609277 < baseStart_3609277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609287 : List Nat := [1, 1, 4, 1, 1, 1, 2, 3, 2, 4, 3]
def baseStart_3609287 : Nat := 118140960795 + 3609287 * 2 ^ 59
def prefixEnd_3609287 : Nat := 4983230072969 + 3 ^ 40 * 3609287 * 2
def baseEnd_3609287 : Nat := 1853299051024325381713697

theorem tailTrace_3609287 : CollatzResearch.WordTrace tailWord_3609287 prefixEnd_3609287 1853299051024325381713697 := by
  unfold tailWord_3609287
  simp only [CollatzResearch.WordTrace]
  refine ⟨131641511675177090989234115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87761007783451393992822743 131641511675177090989234115)
  ·
    refine ⟨197462267512765636483851173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131641511675177090989234115 197462267512765636483851173)
    ·
      refine ⟨37024175158643556840722095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 197462267512765636483851173 37024175158643556840722095)
      ·
        refine ⟨55536262737965335261083143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37024175158643556840722095 55536262737965335261083143)
        ·
          refine ⟨83304394106948002891624715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55536262737965335261083143 83304394106948002891624715)
          ·
            refine ⟨124956591160422004337437073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83304394106948002891624715 124956591160422004337437073)
            ·
              refine ⟨93717443370316503253077805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124956591160422004337437073 93717443370316503253077805)
              ·
                refine ⟨35144041263868688719904177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93717443370316503253077805 35144041263868688719904177)
                ·
                  refine ⟨26358030947901516539928133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35144041263868688719904177 26358030947901516539928133)
                  ·
                    refine ⟨4942130802731534351236525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26358030947901516539928133 4942130802731534351236525)
                    ·
                      refine ⟨1853299051024325381713697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4942130802731534351236525 1853299051024325381713697)
                      ·
                        rfl

theorem cell23_3609287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 4, 3].length) (baseStart_3609287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3609287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3609287 prefixEnd_3609287 := by exact prefixLift 3609287
  have htrace : WordTrace (prefixWord ++ tailWord_3609287) baseStart_3609287 baseEnd_3609287 := by
    simpa [prefixWord, tailWord_3609287, baseEnd_3609287] using wordTrace_append hprefix tailTrace_3609287
  have hstable : (prefixWord ++ tailWord_3609287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609287).length < 2 ^ (prefixWord ++ tailWord_3609287).sum := by decide
  have hdescent : baseEnd_3609287 < baseStart_3609287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609297 : List Nat := [1, 2, 2, 1, 2, 3, 1, 3, 2, 2, 4]
def baseStart_3609297 : Nat := 118140960795 + 3609297 * 2 ^ 59
def prefixEnd_3609297 : Nat := 4983230072969 + 3 ^ 40 * 3609297 * 2
def baseEnd_3609297 : Nat := 1853304185830870342588651

theorem tailTrace_3609297 : CollatzResearch.WordTrace tailWord_3609297 prefixEnd_3609297 1853304185830870342588651 := by
  unfold tailWord_3609297
  simp only [CollatzResearch.WordTrace]
  refine ⟨131641876405140862697098145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87761250936760575131398763 131641876405140862697098145)
  ·
    refine ⟨98731407303855647022823609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131641876405140862697098145 98731407303855647022823609)
    ·
      refine ⟨74048555477891735267117707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98731407303855647022823609 74048555477891735267117707)
      ·
        refine ⟨111072833216837602900676561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74048555477891735267117707 111072833216837602900676561)
        ·
          refine ⟨83304624912628202175507421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111072833216837602900676561 83304624912628202175507421)
          ·
            refine ⟨31239234342235575815815283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83304624912628202175507421 31239234342235575815815283)
            ·
              refine ⟨46858851513353363723722925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31239234342235575815815283 46858851513353363723722925)
              ·
                refine ⟨17572069317507511396396097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46858851513353363723722925 17572069317507511396396097)
                ·
                  refine ⟨13179051988130633547297073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17572069317507511396396097 13179051988130633547297073)
                  ·
                    refine ⟨9884288991097975160472805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13179051988130633547297073 9884288991097975160472805)
                    ·
                      refine ⟨1853304185830870342588651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9884288991097975160472805 1853304185830870342588651)
                      ·
                        rfl

theorem cell23_3609297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 2, 4].length) (baseStart_3609297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3609297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3609297 prefixEnd_3609297 := by exact prefixLift 3609297
  have htrace : WordTrace (prefixWord ++ tailWord_3609297) baseStart_3609297 baseEnd_3609297 := by
    simpa [prefixWord, tailWord_3609297, baseEnd_3609297] using wordTrace_append hprefix tailTrace_3609297
  have hstable : (prefixWord ++ tailWord_3609297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609297).length < 2 ^ (prefixWord ++ tailWord_3609297).sum := by decide
  have hdescent : baseEnd_3609297 < baseStart_3609297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609341 : List Nat := [1, 4, 1, 1, 1, 1, 7, 2, 5]
def baseStart_3609341 : Nat := 118140960795 + 3609341 * 2 ^ 59
def prefixEnd_3609341 : Nat := 4983230072969 + 3 ^ 40 * 3609341 * 2
def baseEnd_3609341 : Nat := 205925197664407574493161

theorem tailTrace_3609341 : CollatzResearch.WordTrace tailWord_3609341 prefixEnd_3609341 205925197664407574493161 := by
  unfold tailWord_3609341
  simp only [CollatzResearch.WordTrace]
  refine ⟨131643481216981458211699877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87762320811320972141133251 131643481216981458211699877)
  ·
    refine ⟨24683152728184023414693727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131643481216981458211699877 24683152728184023414693727)
    ·
      refine ⟨37024729092276035122040591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24683152728184023414693727 37024729092276035122040591)
      ·
        refine ⟨55537093638414052683060887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37024729092276035122040591 55537093638414052683060887)
        ·
          refine ⟨83305640457621079024591331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55537093638414052683060887 83305640457621079024591331)
          ·
            refine ⟨124958460686431618536886997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83305640457621079024591331 124958460686431618536886997)
            ·
              refine ⟨2928713922338241059458289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 124958460686431618536886997 2928713922338241059458289)
              ·
                refine ⟨2196535441753680794593717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2928713922338241059458289 2196535441753680794593717)
                ·
                  refine ⟨205925197664407574493161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2196535441753680794593717 205925197664407574493161)
                  ·
                    rfl

theorem cell23_3609341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7, 2, 5].length) (baseStart_3609341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3609341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3609341 prefixEnd_3609341 := by exact prefixLift 3609341
  have htrace : WordTrace (prefixWord ++ tailWord_3609341) baseStart_3609341 baseEnd_3609341 := by
    simpa [prefixWord, tailWord_3609341, baseEnd_3609341] using wordTrace_append hprefix tailTrace_3609341
  have hstable : (prefixWord ++ tailWord_3609341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609341).length < 2 ^ (prefixWord ++ tailWord_3609341).sum := by decide
  have hdescent : baseEnd_3609341 < baseStart_3609341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609451 : List Nat := [1, 1, 1, 1, 2, 2, 4, 4, 2, 3, 2]
def baseStart_3609451 : Nat := 118140960795 + 3609451 * 2 ^ 59
def prefixEnd_3609451 : Nat := 4983230072969 + 3 ^ 40 * 3609451 * 2
def baseEnd_3609451 : Nat := 1853383261851662740062943

theorem tailTrace_3609451 : CollatzResearch.WordTrace tailWord_3609451 prefixEnd_3609451 1853383261851662740062943 := by
  unfold tailWord_3609451
  simp only [CollatzResearch.WordTrace]
  refine ⟨131647493246582946998204207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87764995497721964665469471 131647493246582946998204207)
  ·
    refine ⟨197471239869874420497306311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131647493246582946998204207 197471239869874420497306311)
    ·
      refine ⟨296206859804811630745959467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197471239869874420497306311 296206859804811630745959467)
      ·
        refine ⟨444310289707217446118939201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296206859804811630745959467 444310289707217446118939201)
        ·
          refine ⟨333232717280413084589204401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 444310289707217446118939201 333232717280413084589204401)
          ·
            refine ⟨249924537960309813441903301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 333232717280413084589204401 249924537960309813441903301)
            ·
              refine ⟨46860850867558090020356869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 249924537960309813441903301 46860850867558090020356869)
              ·
                refine ⟨8786409537667141878816913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46860850867558090020356869 8786409537667141878816913)
                ·
                  refine ⟨6589807153250356409112685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8786409537667141878816913 6589807153250356409112685)
                  ·
                    refine ⟨2471177682468883653417257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6589807153250356409112685 2471177682468883653417257)
                    ·
                      refine ⟨1853383261851662740062943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2471177682468883653417257 1853383261851662740062943)
                      ·
                        rfl

theorem cell23_3609451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 2, 3, 2].length) (baseStart_3609451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3609451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3609451 prefixEnd_3609451 := by exact prefixLift 3609451
  have htrace : WordTrace (prefixWord ++ tailWord_3609451) baseStart_3609451 baseEnd_3609451 := by
    simpa [prefixWord, tailWord_3609451, baseEnd_3609451] using wordTrace_append hprefix tailTrace_3609451
  have hstable : (prefixWord ++ tailWord_3609451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609451).length < 2 ^ (prefixWord ++ tailWord_3609451).sum := by decide
  have hdescent : baseEnd_3609451 < baseStart_3609451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609464 : List Nat := [2, 1, 2, 1, 1, 1, 1, 6, 3, 1, 4]
def baseStart_3609464 : Nat := 118140960795 + 3609464 * 2 ^ 59
def prefixEnd_3609464 : Nat := 4983230072969 + 3 ^ 40 * 3609464 * 2
def baseEnd_3609464 : Nat := 1853389937100171189200383

theorem tailTrace_3609464 : CollatzResearch.WordTrace tailWord_3609464 prefixEnd_3609464 1853389937100171189200383 := by
  unfold tailWord_3609464
  simp only [CollatzResearch.WordTrace]
  refine ⟨65823983697767925109213723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87765311597023900145618297 65823983697767925109213723)
  ·
    refine ⟨98735975546651887663820585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65823983697767925109213723 98735975546651887663820585)
    ·
      refine ⟨74051981659988915747865439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98735975546651887663820585 74051981659988915747865439)
      ·
        refine ⟨111077972489983373621798159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74051981659988915747865439 111077972489983373621798159)
        ·
          refine ⟨166616958734975060432697239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111077972489983373621798159 166616958734975060432697239)
          ·
            refine ⟨249925438102462590649045859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166616958734975060432697239 249925438102462590649045859)
            ·
              refine ⟨374888157153693885973568789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249925438102462590649045859 374888157153693885973568789)
              ·
                refine ⟨17572882366579400905011037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 374888157153693885973568789 17572882366579400905011037)
                ·
                  refine ⟨6589830887467275339379139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17572882366579400905011037 6589830887467275339379139)
                  ·
                    refine ⟨9884746331200913009068709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6589830887467275339379139 9884746331200913009068709)
                    ·
                      refine ⟨1853389937100171189200383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9884746331200913009068709 1853389937100171189200383)
                      ·
                        rfl

theorem cell23_3609464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 3, 1, 4].length) (baseStart_3609464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3609464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3609464 prefixEnd_3609464 := by exact prefixLift 3609464
  have htrace : WordTrace (prefixWord ++ tailWord_3609464) baseStart_3609464 baseEnd_3609464 := by
    simpa [prefixWord, tailWord_3609464, baseEnd_3609464] using wordTrace_append hprefix tailTrace_3609464
  have hstable : (prefixWord ++ tailWord_3609464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609464).length < 2 ^ (prefixWord ++ tailWord_3609464).sum := by decide
  have hdescent : baseEnd_3609464 < baseStart_3609464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609481 : List Nat := [1, 2, 1, 1, 5, 2, 1, 4, 1, 1, 4]
def baseStart_3609481 : Nat := 118140960795 + 3609481 * 2 ^ 59
def prefixEnd_3609481 : Nat := 4983230072969 + 3 ^ 40 * 3609481 * 2
def baseEnd_3609481 : Nat := 1853398666271297622687805

theorem tailTrace_3609481 : CollatzResearch.WordTrace tailWord_3609481 prefixEnd_3609481 1853398666271297622687805 := by
  unfold tailWord_3609481
  simp only [CollatzResearch.WordTrace]
  refine ⟨131648587436474262121796297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87765724957649508081197531 131648587436474262121796297)
  ·
    refine ⟨98736440577355696591347223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131648587436474262121796297 98736440577355696591347223)
    ·
      refine ⟨148104660866033544887020835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98736440577355696591347223 148104660866033544887020835)
      ·
        refine ⟨222156991299050317330531253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148104660866033544887020835 222156991299050317330531253)
        ·
          refine ⟨20827217934285967249737305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 222156991299050317330531253 20827217934285967249737305)
          ·
            refine ⟨15620413450714475437302979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20827217934285967249737305 15620413450714475437302979)
            ·
              refine ⟨23430620176071713155954469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15620413450714475437302979 23430620176071713155954469)
              ·
                refine ⟨4393241283013446216741463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23430620176071713155954469 4393241283013446216741463)
                ·
                  refine ⟨6589861924520169325112195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4393241283013446216741463 6589861924520169325112195)
                  ·
                    refine ⟨9884792886780253987668293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6589861924520169325112195 9884792886780253987668293)
                    ·
                      refine ⟨1853398666271297622687805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9884792886780253987668293 1853398666271297622687805)
                      ·
                        rfl

theorem cell23_3609481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 4, 1, 1, 4].length) (baseStart_3609481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3609481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3609481 prefixEnd_3609481 := by exact prefixLift 3609481
  have htrace : WordTrace (prefixWord ++ tailWord_3609481) baseStart_3609481 baseEnd_3609481 := by
    simpa [prefixWord, tailWord_3609481, baseEnd_3609481] using wordTrace_append hprefix tailTrace_3609481
  have hstable : (prefixWord ++ tailWord_3609481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609481).length < 2 ^ (prefixWord ++ tailWord_3609481).sum := by decide
  have hdescent : baseEnd_3609481 < baseStart_3609481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609501 : List Nat := [1, 4, 2, 1, 2, 1, 4, 1, 1, 1, 5]
def baseStart_3609501 : Nat := 118140960795 + 3609501 * 2 ^ 59
def prefixEnd_3609501 : Nat := 4983230072969 + 3 ^ 40 * 3609501 * 2
def baseEnd_3609501 : Nat := 1853408935884387544437713

theorem tailTrace_3609501 : CollatzResearch.WordTrace tailWord_3609501 prefixEnd_3609501 1853408935884387544437713 := by
  unfold tailWord_3609501
  simp only [CollatzResearch.WordTrace]
  refine ⟨131649316896401805537524357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87766211264267870358349571 131649316896401805537524357)
  ·
    refine ⟨24684246918075338538285817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131649316896401805537524357 24684246918075338538285817)
    ·
      refine ⟨18513185188556503903714363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24684246918075338538285817 18513185188556503903714363)
      ·
        refine ⟨27769777782834755855571545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18513185188556503903714363 27769777782834755855571545)
        ·
          refine ⟨20827333337126066891678659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27769777782834755855571545 20827333337126066891678659)
          ·
            refine ⟨31241000005689100337517989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20827333337126066891678659 31241000005689100337517989)
            ·
              refine ⟨5857687501066706313284623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31241000005689100337517989 5857687501066706313284623)
              ·
                refine ⟨8786531251600059469926935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5857687501066706313284623 8786531251600059469926935)
                ·
                  refine ⟨13179796877400089204890403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8786531251600059469926935 13179796877400089204890403)
                  ·
                    refine ⟨19769695316100133807335605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13179796877400089204890403 19769695316100133807335605)
                    ·
                      refine ⟨1853408935884387544437713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19769695316100133807335605 1853408935884387544437713)
                      ·
                        rfl

theorem cell23_3609501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_3609501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3609501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3609501 prefixEnd_3609501 := by exact prefixLift 3609501
  have htrace : WordTrace (prefixWord ++ tailWord_3609501) baseStart_3609501 baseEnd_3609501 := by
    simpa [prefixWord, tailWord_3609501, baseEnd_3609501] using wordTrace_append hprefix tailTrace_3609501
  have hstable : (prefixWord ++ tailWord_3609501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609501).length < 2 ^ (prefixWord ++ tailWord_3609501).sum := by decide
  have hdescent : baseEnd_3609501 < baseStart_3609501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609521 : List Nat := [1, 2, 2, 4, 3, 1, 2, 8]
def baseStart_3609521 : Nat := 118140960795 + 3609521 * 2 ^ 59
def prefixEnd_3609521 : Nat := 4983230072969 + 3 ^ 40 * 3609521 * 2
def baseEnd_3609521 : Nat := 68645155759165832081023

theorem tailTrace_3609521 : CollatzResearch.WordTrace tailWord_3609521 prefixEnd_3609521 68645155759165832081023 := by
  unfold tailWord_3609521
  simp only [CollatzResearch.WordTrace]
  refine ⟨131650046356329348953252417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87766697570886232635501611 131650046356329348953252417)
  ·
    refine ⟨98737534767247011714939313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131650046356329348953252417 98737534767247011714939313)
    ·
      refine ⟨74053151075435258786204485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98737534767247011714939313 74053151075435258786204485)
      ·
        refine ⟨13884965826644111022413341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74053151075435258786204485 13884965826644111022413341)
        ·
          refine ⟨5206862184991541633405003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13884965826644111022413341 5206862184991541633405003)
          ·
            refine ⟨7810293277487312450107505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5206862184991541633405003 7810293277487312450107505)
            ·
              refine ⟨5857719958115484337580629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7810293277487312450107505 5857719958115484337580629)
              ·
                refine ⟨68645155759165832081023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5857719958115484337580629 68645155759165832081023)
                ·
                  rfl

theorem cell23_3609521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 8].length) (baseStart_3609521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3609521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3609521 prefixEnd_3609521 := by exact prefixLift 3609521
  have htrace : WordTrace (prefixWord ++ tailWord_3609521) baseStart_3609521 baseEnd_3609521 := by
    simpa [prefixWord, tailWord_3609521, baseEnd_3609521] using wordTrace_append hprefix tailTrace_3609521
  have hstable : (prefixWord ++ tailWord_3609521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609521).length < 2 ^ (prefixWord ++ tailWord_3609521).sum := by decide
  have hdescent : baseEnd_3609521 < baseStart_3609521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609565 : List Nat := [1, 4, 3, 1, 2, 1, 1, 4, 2, 1, 3]
def baseStart_3609565 : Nat := 118140960795 + 3609565 * 2 ^ 59
def prefixEnd_3609565 : Nat := 4983230072969 + 3 ^ 40 * 3609565 * 2
def baseEnd_3609565 : Nat := 1853441798646275294037419

theorem tailTrace_3609565 : CollatzResearch.WordTrace tailWord_3609565 prefixEnd_3609565 1853441798646275294037419 := by
  unfold tailWord_3609565
  simp only [CollatzResearch.WordTrace]
  refine ⟨131651651168169944467854149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87767767445446629645236099 131651651168169944467854149)
  ·
    refine ⟨24684684594031864587722653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131651651168169944467854149 24684684594031864587722653)
    ·
      refine ⟨9256756722761949220395995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24684684594031864587722653 9256756722761949220395995)
      ·
        refine ⟨13885135084142923830593993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9256756722761949220395995 13885135084142923830593993)
        ·
          refine ⟨10413851313107192872945495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13885135084142923830593993 10413851313107192872945495)
          ·
            refine ⟨15620776969660789309418243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10413851313107192872945495 15620776969660789309418243)
            ·
              refine ⟨23431165454491183964127365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15620776969660789309418243 23431165454491183964127365)
              ·
                refine ⟨4393343522717096993273881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23431165454491183964127365 4393343522717096993273881)
                ·
                  refine ⟨3295007642037822744955411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4393343522717096993273881 3295007642037822744955411)
                  ·
                    refine ⟨4942511463056734117433117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3295007642037822744955411 4942511463056734117433117)
                    ·
                      refine ⟨1853441798646275294037419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4942511463056734117433117 1853441798646275294037419)
                      ·
                        rfl

theorem cell23_3609565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_3609565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3609565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3609565 prefixEnd_3609565 := by exact prefixLift 3609565
  have htrace : WordTrace (prefixWord ++ tailWord_3609565) baseStart_3609565 baseEnd_3609565 := by
    simpa [prefixWord, tailWord_3609565, baseEnd_3609565] using wordTrace_append hprefix tailTrace_3609565
  have hstable : (prefixWord ++ tailWord_3609565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609565).length < 2 ^ (prefixWord ++ tailWord_3609565).sum := by decide
  have hdescent : baseEnd_3609565 < baseStart_3609565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609628 : List Nat := [2, 2, 3, 1, 4, 1, 2, 1, 7]
def baseStart_3609628 : Nat := 118140960795 + 3609628 * 2 ^ 59
def prefixEnd_3609628 : Nat := 4983230072969 + 3 ^ 40 * 3609628 * 2
def baseEnd_3609628 : Nat := 205941571991945394172181

theorem tailTrace_3609628 : CollatzResearch.WordTrace tailWord_3609628 prefixEnd_3609628 205941571991945394172181 := by
  unfold tailWord_3609628
  simp only [CollatzResearch.WordTrace]
  refine ⟨65826974483470853113698769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87769299311294470818265025 65826974483470853113698769)
  ·
    refine ⟨49370230862603139835274077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65826974483470853113698769 49370230862603139835274077)
    ·
      refine ⟨18513836573476177438227779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49370230862603139835274077 18513836573476177438227779)
      ·
        refine ⟨27770754860214266157341669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18513836573476177438227779 27770754860214266157341669)
        ·
          refine ⟨5207016536290174904501563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27770754860214266157341669 5207016536290174904501563)
          ·
            refine ⟨7810524804435262356752345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5207016536290174904501563 7810524804435262356752345)
            ·
              refine ⟨5857893603326446767564259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7810524804435262356752345 5857893603326446767564259)
              ·
                refine ⟨8786840404989670151346389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5857893603326446767564259 8786840404989670151346389)
                ·
                  refine ⟨205941571991945394172181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8786840404989670151346389 205941571991945394172181)
                  ·
                    rfl

theorem cell23_3609628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 1, 7].length) (baseStart_3609628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3609628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3609628 prefixEnd_3609628 := by exact prefixLift 3609628
  have htrace : WordTrace (prefixWord ++ tailWord_3609628) baseStart_3609628 baseEnd_3609628 := by
    simpa [prefixWord, tailWord_3609628, baseEnd_3609628] using wordTrace_append hprefix tailTrace_3609628
  have hstable : (prefixWord ++ tailWord_3609628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609628).length < 2 ^ (prefixWord ++ tailWord_3609628).sum := by decide
  have hdescent : baseEnd_3609628 < baseStart_3609628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609662 : List Nat := [4, 2, 1, 3, 1, 3, 1, 3, 5]
def baseStart_3609662 : Nat := 118140960795 + 3609662 * 2 ^ 59
def prefixEnd_3609662 : Nat := 4983230072969 + 3 ^ 40 * 3609662 * 2
def baseEnd_3609662 : Nat := 205943511807751268280497

theorem tailTrace_3609662 : CollatzResearch.WordTrace tailWord_3609662 prefixEnd_3609662 205943511807751268280497 := by
  unfold tailWord_3609662
  simp only [CollatzResearch.WordTrace]
  refine ⟨16456898631102316254266905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87770126032545686689423493 16456898631102316254266905)
  ·
    refine ⟨12342673973326737190700179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16456898631102316254266905 12342673973326737190700179)
    ·
      refine ⟨18514010959990105786050269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12342673973326737190700179 18514010959990105786050269)
      ·
        refine ⟨6942754109996289669768851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18514010959990105786050269 6942754109996289669768851)
        ·
          refine ⟨10414131164994434504653277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6942754109996289669768851 10414131164994434504653277)
          ·
            refine ⟨3905299186872912939244979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10414131164994434504653277 3905299186872912939244979)
            ·
              refine ⟨5857948780309369408867469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3905299186872912939244979 5857948780309369408867469)
              ·
                refine ⟨2196730792616013528325301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5857948780309369408867469 2196730792616013528325301)
                ·
                  refine ⟨205943511807751268280497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2196730792616013528325301 205943511807751268280497)
                  ·
                    rfl

theorem cell23_3609662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 3, 5].length) (baseStart_3609662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3609662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3609662 prefixEnd_3609662 := by exact prefixLift 3609662
  have htrace : WordTrace (prefixWord ++ tailWord_3609662) baseStart_3609662 baseEnd_3609662 := by
    simpa [prefixWord, tailWord_3609662, baseEnd_3609662] using wordTrace_append hprefix tailTrace_3609662
  have hstable : (prefixWord ++ tailWord_3609662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609662).length < 2 ^ (prefixWord ++ tailWord_3609662).sum := by decide
  have hdescent : baseEnd_3609662 < baseStart_3609662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609678 : List Nat := [4, 1, 1, 1, 1, 3, 3, 2, 2, 1, 4]
def baseStart_3609678 : Nat := 118140960795 + 3609678 * 2 ^ 59
def prefixEnd_3609678 : Nat := 4983230072969 + 3 ^ 40 * 3609678 * 2
def baseEnd_3609678 : Nat := 1853499821960233351924399

theorem tailTrace_3609678 : CollatzResearch.WordTrace tailWord_3609678 prefixEnd_3609678 1853499821960233351924399 := by
  unfold tailWord_3609678
  simp only [CollatzResearch.WordTrace]
  refine ⟨16456971577095070595839711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87770515077840376511145125 16456971577095070595839711)
  ·
    refine ⟨24685457365642605893759567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16456971577095070595839711 24685457365642605893759567)
    ·
      refine ⟨37028186048463908840639351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24685457365642605893759567 37028186048463908840639351)
      ·
        refine ⟨55542279072695863260959027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37028186048463908840639351 55542279072695863260959027)
        ·
          refine ⟨83313418609043794891438541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55542279072695863260959027 83313418609043794891438541)
          ·
            refine ⟨31242531978391423084289453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83313418609043794891438541 31242531978391423084289453)
            ·
              refine ⟨11715949491896783656608545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31242531978391423084289453 11715949491896783656608545)
              ·
                refine ⟨8786962118922587742456409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11715949491896783656608545 8786962118922587742456409)
                ·
                  refine ⟨6590221589191940806842307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8786962118922587742456409 6590221589191940806842307)
                  ·
                    refine ⟨9885332383787911210263461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6590221589191940806842307 9885332383787911210263461)
                    ·
                      refine ⟨1853499821960233351924399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9885332383787911210263461 1853499821960233351924399)
                      ·
                        rfl

theorem cell23_3609678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 2, 2, 1, 4].length) (baseStart_3609678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3609678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3609678 prefixEnd_3609678 := by exact prefixLift 3609678
  have htrace : WordTrace (prefixWord ++ tailWord_3609678) baseStart_3609678 baseEnd_3609678 := by
    simpa [prefixWord, tailWord_3609678, baseEnd_3609678] using wordTrace_append hprefix tailTrace_3609678
  have hstable : (prefixWord ++ tailWord_3609678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609678).length < 2 ^ (prefixWord ++ tailWord_3609678).sum := by decide
  have hdescent : baseEnd_3609678 < baseStart_3609678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609778 : List Nat := [3, 2, 1, 1, 1, 4, 2, 2, 1, 6]
def baseStart_3609778 : Nat := 118140960795 + 3609778 * 2 ^ 59
def prefixEnd_3609778 : Nat := 4983230072969 + 3 ^ 40 * 3609778 * 2
def baseEnd_3609778 : Nat := 617850390008560986891313

theorem tailTrace_3609778 : CollatzResearch.WordTrace tailWord_3609778 prefixEnd_3609778 617850390008560986891313 := by
  unfold tailWord_3609778
  simp only [CollatzResearch.WordTrace]
  refine ⟨32914854979099570461339497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87772946610932187896905325 32914854979099570461339497)
  ·
    refine ⟨24686141234324677846004623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32914854979099570461339497 24686141234324677846004623)
    ·
      refine ⟨37029211851487016769006935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24686141234324677846004623 37029211851487016769006935)
      ·
        refine ⟨55543817777230525153510403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37029211851487016769006935 55543817777230525153510403)
        ·
          refine ⟨83315726665845787730265605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55543817777230525153510403 83315726665845787730265605)
          ·
            refine ⟨15621698749846085199424801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83315726665845787730265605 15621698749846085199424801)
            ·
              refine ⟨11716274062384563899568601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15621698749846085199424801 11716274062384563899568601)
              ·
                refine ⟨8787205546788422924676451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11716274062384563899568601 8787205546788422924676451)
                ·
                  refine ⟨13180808320182634387014677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8787205546788422924676451 13180808320182634387014677)
                  ·
                    refine ⟨617850390008560986891313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13180808320182634387014677 617850390008560986891313)
                    ·
                      rfl

theorem cell23_3609778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 2, 1, 6].length) (baseStart_3609778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3609778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3609778 prefixEnd_3609778 := by exact prefixLift 3609778
  have htrace : WordTrace (prefixWord ++ tailWord_3609778) baseStart_3609778 baseEnd_3609778 := by
    simpa [prefixWord, tailWord_3609778, baseEnd_3609778] using wordTrace_append hprefix tailTrace_3609778
  have hstable : (prefixWord ++ tailWord_3609778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609778).length < 2 ^ (prefixWord ++ tailWord_3609778).sum := by decide
  have hdescent : baseEnd_3609778 < baseStart_3609778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609785 : List Nat := [1, 2, 1, 4, 1, 4, 1, 3, 1, 1, 4]
def baseStart_3609785 : Nat := 118140960795 + 3609785 * 2 ^ 59
def prefixEnd_3609785 : Nat := 4983230072969 + 3 ^ 40 * 3609785 * 2
def baseEnd_3609785 : Nat := 1853554764390264433286407

theorem tailTrace_3609785 : CollatzResearch.WordTrace tailWord_3609785 prefixEnd_3609785 1853554764390264433286407 := by
  unfold tailWord_3609785
  simp only [CollatzResearch.WordTrace]
  refine ⟨131659675227372922040862809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87773116818248614693908539 131659675227372922040862809)
  ·
    refine ⟨98744756420529691530647107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131659675227372922040862809 98744756420529691530647107)
    ·
      refine ⟨148117134630794537295970661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98744756420529691530647107 148117134630794537295970661)
      ·
        refine ⟨27771962743273975742994499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148117134630794537295970661 27771962743273975742994499)
        ·
          refine ⟨41657944114910963614491749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27771962743273975742994499 41657944114910963614491749)
          ·
            refine ⟨7810864521545805677717203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41657944114910963614491749 7810864521545805677717203)
            ·
              refine ⟨11716296782318708516575805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7810864521545805677717203 11716296782318708516575805)
              ·
                refine ⟨4393611293369515693715927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11716296782318708516575805 4393611293369515693715927)
                ·
                  refine ⟨6590416940054273540573891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4393611293369515693715927 6590416940054273540573891)
                  ·
                    refine ⟨9885625410081410310860837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6590416940054273540573891 9885625410081410310860837)
                    ·
                      refine ⟨1853554764390264433286407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9885625410081410310860837 1853554764390264433286407)
                      ·
                        rfl

theorem cell23_3609785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 3, 1, 1, 4].length) (baseStart_3609785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3609785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3609785 prefixEnd_3609785 := by exact prefixLift 3609785
  have htrace : WordTrace (prefixWord ++ tailWord_3609785) baseStart_3609785 baseEnd_3609785 := by
    simpa [prefixWord, tailWord_3609785, baseEnd_3609785] using wordTrace_append hprefix tailTrace_3609785
  have hstable : (prefixWord ++ tailWord_3609785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609785).length < 2 ^ (prefixWord ++ tailWord_3609785).sum := by decide
  have hdescent : baseEnd_3609785 < baseStart_3609785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609802 : List Nat := [3, 1, 2, 1, 3, 2, 1, 3, 3, 2, 2]
def baseStart_3609802 : Nat := 118140960795 + 3609802 * 2 ^ 59
def prefixEnd_3609802 : Nat := 4983230072969 + 3 ^ 40 * 3609802 * 2
def baseEnd_3609802 : Nat := 1853563493561390866773829

theorem tailTrace_3609802 : CollatzResearch.WordTrace tailWord_3609802 prefixEnd_3609802 1853563493561390866773829 := by
  unfold tailWord_3609802
  simp only [CollatzResearch.WordTrace]
  refine ⟨32915073817077833486057915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87773530178874222629487773 32915073817077833486057915)
  ·
    refine ⟨49372610725616750229086873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32915073817077833486057915 49372610725616750229086873)
    ·
      refine ⟨37029458044212562671815155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49372610725616750229086873 37029458044212562671815155)
      ·
        refine ⟨55544187066318844007722733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37029458044212562671815155 55544187066318844007722733)
        ·
          refine ⟨20829070149869566502896025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55544187066318844007722733 20829070149869566502896025)
          ·
            refine ⟨15621802612402174877172019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20829070149869566502896025 15621802612402174877172019)
            ·
              refine ⟨23432703918603262315758029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15621802612402174877172019 23432703918603262315758029)
              ·
                refine ⟨8787263969476223368409261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23432703918603262315758029 8787263969476223368409261)
                ·
                  refine ⟨3295223988553583763153473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8787263969476223368409261 3295223988553583763153473)
                  ·
                    refine ⟨2471417991415187822365105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3295223988553583763153473 2471417991415187822365105)
                    ·
                      refine ⟨1853563493561390866773829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2471417991415187822365105 1853563493561390866773829)
                      ·
                        rfl

theorem cell23_3609802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 3, 3, 2, 2].length) (baseStart_3609802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3609802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3609802 prefixEnd_3609802 := by exact prefixLift 3609802
  have htrace : WordTrace (prefixWord ++ tailWord_3609802) baseStart_3609802 baseEnd_3609802 := by
    simpa [prefixWord, tailWord_3609802, baseEnd_3609802] using wordTrace_append hprefix tailTrace_3609802
  have hstable : (prefixWord ++ tailWord_3609802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609802).length < 2 ^ (prefixWord ++ tailWord_3609802).sum := by decide
  have hdescent : baseEnd_3609802 < baseStart_3609802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609811 : List Nat := [1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 6]
def baseStart_3609811 : Nat := 118140960795 + 3609811 * 2 ^ 59
def prefixEnd_3609811 : Nat := 4983230072969 + 3 ^ 40 * 3609811 * 2
def baseEnd_3609811 : Nat := 1853568114887281331561287

theorem tailTrace_3609811 : CollatzResearch.WordTrace tailWord_3609811 prefixEnd_3609811 1853568114887281331561287 := by
  unfold tailWord_3609811
  simp only [CollatzResearch.WordTrace]
  refine ⟨131660623525278728481309287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87773749016852485654206191 131660623525278728481309287)
  ·
    refine ⟨197490935287918092721963931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131660623525278728481309287 197490935287918092721963931)
    ·
      refine ⟨296236402931877139082945897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197490935287918092721963931 296236402931877139082945897)
      ·
        refine ⟨222177302198907854312209423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296236402931877139082945897 222177302198907854312209423)
        ·
          refine ⟨333265953298361781468314135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222177302198907854312209423 333265953298361781468314135)
          ·
            refine ⟨499898929947542672202471203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333265953298361781468314135 499898929947542672202471203)
            ·
              refine ⟨749848394921314008303706805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 499898929947542672202471203 749848394921314008303706805)
              ·
                refine ⟨70298287023873188278472513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 749848394921314008303706805 70298287023873188278472513)
                ·
                  refine ⟨52723715267904891208854385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70298287023873188278472513 52723715267904891208854385)
                  ·
                    refine ⟨39542786450928668406640789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52723715267904891208854385 39542786450928668406640789)
                    ·
                      refine ⟨1853568114887281331561287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39542786450928668406640789 1853568114887281331561287)
                      ·
                        rfl

theorem cell23_3609811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 6].length) (baseStart_3609811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3609811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3609811 prefixEnd_3609811 := by exact prefixLift 3609811
  have htrace : WordTrace (prefixWord ++ tailWord_3609811) baseStart_3609811 baseEnd_3609811 := by
    simpa [prefixWord, tailWord_3609811, baseEnd_3609811] using wordTrace_append hprefix tailTrace_3609811
  have hstable : (prefixWord ++ tailWord_3609811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609811).length < 2 ^ (prefixWord ++ tailWord_3609811).sum := by decide
  have hdescent : baseEnd_3609811 < baseStart_3609811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609825 : List Nat := [1, 2, 3, 1, 3, 4, 2, 7]
def baseStart_3609825 : Nat := 118140960795 + 3609825 * 2 ^ 59
def prefixEnd_3609825 : Nat := 4983230072969 + 3 ^ 40 * 3609825 * 2
def baseEnd_3609825 : Nat := 68650937170979417658749

theorem tailTrace_3609825 : CollatzResearch.WordTrace tailWord_3609825 prefixEnd_3609825 68650937170979417658749 := by
  unfold tailWord_3609825
  simp only [CollatzResearch.WordTrace]
  refine ⟨131661134147228008872318929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87774089431485339248212619 131661134147228008872318929)
  ·
    refine ⟨98745850610421006654239197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131661134147228008872318929 98745850610421006654239197)
    ·
      refine ⟨37029693978907877495339699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98745850610421006654239197 37029693978907877495339699)
      ·
        refine ⟨55544540968361816243009549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37029693978907877495339699 55544540968361816243009549)
        ·
          refine ⟨20829202863135681091128581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55544540968361816243009549 20829202863135681091128581)
          ·
            refine ⟨3905475536837940204586609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20829202863135681091128581 3905475536837940204586609)
            ·
              refine ⟨2929106652628455153439957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3905475536837940204586609 2929106652628455153439957)
              ·
                refine ⟨68650937170979417658749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2929106652628455153439957 68650937170979417658749)
                ·
                  rfl

theorem cell23_3609825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2, 7].length) (baseStart_3609825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3609825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3609825 prefixEnd_3609825 := by exact prefixLift 3609825
  have htrace : WordTrace (prefixWord ++ tailWord_3609825) baseStart_3609825 baseEnd_3609825 := by
    simpa [prefixWord, tailWord_3609825, baseEnd_3609825] using wordTrace_append hprefix tailTrace_3609825
  have hstable : (prefixWord ++ tailWord_3609825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609825).length < 2 ^ (prefixWord ++ tailWord_3609825).sum := by decide
  have hdescent : baseEnd_3609825 < baseStart_3609825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609835 : List Nat := [1, 1, 1, 1, 2, 6, 1, 2, 4, 1, 3]
def baseStart_3609835 : Nat := 118140960795 + 3609835 * 2 ^ 59
def prefixEnd_3609835 : Nat := 4983230072969 + 3 ^ 40 * 3609835 * 2
def baseEnd_3609835 : Nat := 1853580438422989237661177

theorem tailTrace_3609835 : CollatzResearch.WordTrace tailWord_3609835 prefixEnd_3609835 1853580438422989237661177 := by
  unfold tailWord_3609835
  simp only [CollatzResearch.WordTrace]
  refine ⟨131661498877191780580182959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87774332584794520386788639 131661498877191780580182959)
  ·
    refine ⟨197492248315787670870274439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131661498877191780580182959 197492248315787670870274439)
    ·
      refine ⟨296238372473681506305411659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197492248315787670870274439 296238372473681506305411659)
      ·
        refine ⟨444357558710522259458117489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296238372473681506305411659 444357558710522259458117489)
        ·
          refine ⟨333268169032891694593588117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 444357558710522259458117489 333268169032891694593588117)
          ·
            refine ⟨15621945423416798184074443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 333268169032891694593588117 15621945423416798184074443)
            ·
              refine ⟨23432918135125197276111665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15621945423416798184074443 23432918135125197276111665)
              ·
                refine ⟨17574688601343897957083749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23432918135125197276111665 17574688601343897957083749)
                ·
                  refine ⟨3295254112751980866953203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17574688601343897957083749 3295254112751980866953203)
                  ·
                    refine ⟨4942881169127971300429805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3295254112751980866953203 4942881169127971300429805)
                    ·
                      refine ⟨1853580438422989237661177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4942881169127971300429805 1853580438422989237661177)
                      ·
                        rfl

theorem cell23_3609835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 4, 1, 3].length) (baseStart_3609835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3609835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3609835 prefixEnd_3609835 := by exact prefixLift 3609835
  have htrace : WordTrace (prefixWord ++ tailWord_3609835) baseStart_3609835 baseEnd_3609835 := by
    simpa [prefixWord, tailWord_3609835, baseEnd_3609835] using wordTrace_append hprefix tailTrace_3609835
  have hstable : (prefixWord ++ tailWord_3609835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609835).length < 2 ^ (prefixWord ++ tailWord_3609835).sum := by decide
  have hdescent : baseEnd_3609835 < baseStart_3609835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609836 : List Nat := [2, 2, 1, 1, 2, 6, 1, 3, 1, 2, 2]
def baseStart_3609836 : Nat := 118140960795 + 3609836 * 2 ^ 59
def prefixEnd_3609836 : Nat := 4983230072969 + 3 ^ 40 * 3609836 * 2
def baseEnd_3609836 : Nat := 1853580951903643733748673

theorem tailTrace_3609836 : CollatzResearch.WordTrace tailWord_3609836 prefixEnd_3609836 1853580951903643733748673 := by
  unfold tailWord_3609836
  simp only [CollatzResearch.WordTrace]
  refine ⟨65830767675094078875484681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87774356900125438500646241 65830767675094078875484681)
  ·
    refine ⟨49373075756320559156613511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65830767675094078875484681 49373075756320559156613511)
    ·
      refine ⟨74059613634480838734920267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49373075756320559156613511 74059613634480838734920267)
      ·
        refine ⟨111089420451721258102380401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74059613634480838734920267 111089420451721258102380401)
        ·
          refine ⟨83317065338790943576785301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111089420451721258102380401 83317065338790943576785301)
          ·
            refine ⟨3905487437755825480161811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 83317065338790943576785301 3905487437755825480161811)
            ·
              refine ⟨5858231156633738220242717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3905487437755825480161811 5858231156633738220242717)
              ·
                refine ⟨2196836683737651832591019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5858231156633738220242717 2196836683737651832591019)
                ·
                  refine ⟨3295255025606477748886529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2196836683737651832591019 3295255025606477748886529)
                  ·
                    refine ⟨2471441269204858311664897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3295255025606477748886529 2471441269204858311664897)
                    ·
                      refine ⟨1853580951903643733748673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2471441269204858311664897 1853580951903643733748673)
                      ·
                        rfl

theorem cell23_3609836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 3, 1, 2, 2].length) (baseStart_3609836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3609836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3609836 prefixEnd_3609836 := by exact prefixLift 3609836
  have htrace : WordTrace (prefixWord ++ tailWord_3609836) baseStart_3609836 baseEnd_3609836 := by
    simpa [prefixWord, tailWord_3609836, baseEnd_3609836] using wordTrace_append hprefix tailTrace_3609836
  have hstable : (prefixWord ++ tailWord_3609836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609836).length < 2 ^ (prefixWord ++ tailWord_3609836).sum := by decide
  have hdescent : baseEnd_3609836 < baseStart_3609836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609892 : List Nat := [2, 3, 1, 3, 1, 1, 3, 2, 1, 4, 2]
def baseStart_3609892 : Nat := 118140960795 + 3609892 * 2 ^ 59
def prefixEnd_3609892 : Nat := 4983230072969 + 3 ^ 40 * 3609892 * 2
def baseEnd_3609892 : Nat := 1853609706820295514648415

theorem tailTrace_3609892 : CollatzResearch.WordTrace tailWord_3609892 prefixEnd_3609892 1853609706820295514648415 := by
  unfold tailWord_3609892
  simp only [CollatzResearch.WordTrace]
  refine ⟨65831788918992639657503965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87775718558656852876671953 65831788918992639657503965)
  ·
    refine ⟨24686920844622239871563987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65831788918992639657503965 24686920844622239871563987)
    ·
      refine ⟨37030381266933359807345981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24686920844622239871563987 37030381266933359807345981)
      ·
        refine ⟨13886392975100009927754743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37030381266933359807345981 13886392975100009927754743)
        ·
          refine ⟨20829589462650014891632115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13886392975100009927754743 20829589462650014891632115)
          ·
            refine ⟨31244384193975022337448173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20829589462650014891632115 31244384193975022337448173)
            ·
              refine ⟨11716644072740633376543065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31244384193975022337448173 11716644072740633376543065)
              ·
                refine ⟨8787483054555475032407299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11716644072740633376543065 8787483054555475032407299)
                ·
                  refine ⟨13181224581833212548610949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8787483054555475032407299 13181224581833212548610949)
                  ·
                    refine ⟨2471479609093727352864553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13181224581833212548610949 2471479609093727352864553)
                    ·
                      refine ⟨1853609706820295514648415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2471479609093727352864553 1853609706820295514648415)
                      ·
                        rfl

theorem cell23_3609892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_3609892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3609892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3609892 prefixEnd_3609892 := by exact prefixLift 3609892
  have htrace : WordTrace (prefixWord ++ tailWord_3609892) baseStart_3609892 baseEnd_3609892 := by
    simpa [prefixWord, tailWord_3609892, baseEnd_3609892] using wordTrace_append hprefix tailTrace_3609892
  have hstable : (prefixWord ++ tailWord_3609892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609892).length < 2 ^ (prefixWord ++ tailWord_3609892).sum := by decide
  have hdescent : baseEnd_3609892 < baseStart_3609892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609896 : List Nat := [2, 1, 5, 1, 2, 2, 3, 1, 1, 3, 2]
def baseStart_3609896 : Nat := 118140960795 + 3609896 * 2 ^ 59
def prefixEnd_3609896 : Nat := 4983230072969 + 3 ^ 40 * 3609896 * 2
def baseEnd_3609896 : Nat := 1853611760742913498998397

theorem tailTrace_3609896 : CollatzResearch.WordTrace tailWord_3609896 prefixEnd_3609896 1853611760742913498998397 := by
  unfold tailWord_3609896
  simp only [CollatzResearch.WordTrace]
  refine ⟨65831861864985393999076771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87775815819980525332102361 65831861864985393999076771)
  ·
    refine ⟨98747792797478090998615157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65831861864985393999076771 98747792797478090998615157)
    ·
      refine ⟨9257605574763571031120171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98747792797478090998615157 9257605574763571031120171)
      ·
        refine ⟨13886408362145356546680257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9257605574763571031120171 13886408362145356546680257)
        ·
          refine ⟨10414806271609017410010193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13886408362145356546680257 10414806271609017410010193)
          ·
            refine ⟨7811104703706763057507645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10414806271609017410010193 7811104703706763057507645)
            ·
              refine ⟨2929164263890036146565367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7811104703706763057507645 2929164263890036146565367)
              ·
                refine ⟨4393746395835054219848051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2929164263890036146565367 4393746395835054219848051)
                ·
                  refine ⟨6590619593752581329772077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4393746395835054219848051 6590619593752581329772077)
                  ·
                    refine ⟨2471482347657217998664529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6590619593752581329772077 2471482347657217998664529)
                    ·
                      refine ⟨1853611760742913498998397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2471482347657217998664529 1853611760742913498998397)
                      ·
                        rfl

theorem cell23_3609896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_3609896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3609896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3609896 prefixEnd_3609896 := by exact prefixLift 3609896
  have htrace : WordTrace (prefixWord ++ tailWord_3609896) baseStart_3609896 baseEnd_3609896 := by
    simpa [prefixWord, tailWord_3609896, baseEnd_3609896] using wordTrace_append hprefix tailTrace_3609896
  have hstable : (prefixWord ++ tailWord_3609896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609896).length < 2 ^ (prefixWord ++ tailWord_3609896).sum := by decide
  have hdescent : baseEnd_3609896 < baseStart_3609896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609909 : List Nat := [1, 3, 3, 1, 2, 2, 1, 4, 2, 2, 2]
def baseStart_3609909 : Nat := 118140960795 + 3609909 * 2 ^ 59
def prefixEnd_3609909 : Nat := 4983230072969 + 3 ^ 40 * 3609909 * 2
def baseEnd_3609909 : Nat := 1853618435991421948135837

theorem tailTrace_3609909 : CollatzResearch.WordTrace tailWord_3609909 prefixEnd_3609909 1853618435991421948135837 := by
  unfold tailWord_3609909
  simp only [CollatzResearch.WordTrace]
  refine ⟨131664197878923691218376781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87776131919282460812251187 131664197878923691218376781)
  ·
    refine ⟨49374074204596384206891293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131664197878923691218376781 49374074204596384206891293)
    ·
      refine ⟨18515277826723644077584235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49374074204596384206891293 18515277826723644077584235)
      ·
        refine ⟨27772916740085466116376353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18515277826723644077584235 27772916740085466116376353)
        ·
          refine ⟨20829687555064099587282265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27772916740085466116376353 20829687555064099587282265)
          ·
            refine ⟨15622265666298074690461699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20829687555064099587282265 15622265666298074690461699)
            ·
              refine ⟨23433398499447112035692549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15622265666298074690461699 23433398499447112035692549)
              ·
                refine ⟨4393762218646333506692353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23433398499447112035692549 4393762218646333506692353)
                ·
                  refine ⟨3295321663984750130019265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4393762218646333506692353 3295321663984750130019265)
                  ·
                    refine ⟨2471491247988562597514449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3295321663984750130019265 2471491247988562597514449)
                    ·
                      refine ⟨1853618435991421948135837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2471491247988562597514449 1853618435991421948135837)
                      ·
                        rfl

theorem cell23_3609909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 4, 2, 2, 2].length) (baseStart_3609909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3609909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3609909 prefixEnd_3609909 := by exact prefixLift 3609909
  have htrace : WordTrace (prefixWord ++ tailWord_3609909) baseStart_3609909 baseEnd_3609909 := by
    simpa [prefixWord, tailWord_3609909, baseEnd_3609909] using wordTrace_append hprefix tailTrace_3609909
  have hstable : (prefixWord ++ tailWord_3609909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609909).length < 2 ^ (prefixWord ++ tailWord_3609909).sum := by decide
  have hdescent : baseEnd_3609909 < baseStart_3609909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609928 : List Nat := [2, 1, 3, 1, 1, 2, 1, 4, 1, 7]
def baseStart_3609928 : Nat := 118140960795 + 3609928 * 2 ^ 59
def prefixEnd_3609928 : Nat := 4983230072969 + 3 ^ 40 * 3609928 * 2
def baseEnd_3609928 : Nat := 617876064041285791266083

theorem tailTrace_3609928 : CollatzResearch.WordTrace tailWord_3609928 prefixEnd_3609928 617876064041285791266083 := by
  unfold tailWord_3609928
  simp only [CollatzResearch.WordTrace]
  refine ⟨65832445432927428731659219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87776593910569904975545625 65832445432927428731659219)
  ·
    refine ⟨98748668149391143097488829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65832445432927428731659219 98748668149391143097488829)
    ·
      refine ⟨37030750556021678661558311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98748668149391143097488829 37030750556021678661558311)
      ·
        refine ⟨55546125834032517992337467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37030750556021678661558311 55546125834032517992337467)
        ·
          refine ⟨83319188751048776988506201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55546125834032517992337467 83319188751048776988506201)
          ·
            refine ⟨62489391563286582741379651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83319188751048776988506201 62489391563286582741379651)
            ·
              refine ⟨93734087344929874112069477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62489391563286582741379651 93734087344929874112069477)
              ·
                refine ⟨17575141377174351396013027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93734087344929874112069477 17575141377174351396013027)
                ·
                  refine ⟨26362712065761527094019541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17575141377174351396013027 26362712065761527094019541)
                  ·
                    refine ⟨617876064041285791266083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26362712065761527094019541 617876064041285791266083)
                    ·
                      rfl

theorem cell23_3609928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 1, 7].length) (baseStart_3609928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3609928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3609928 prefixEnd_3609928 := by exact prefixLift 3609928
  have htrace : WordTrace (prefixWord ++ tailWord_3609928) baseStart_3609928 baseEnd_3609928 := by
    simpa [prefixWord, tailWord_3609928, baseEnd_3609928] using wordTrace_append hprefix tailTrace_3609928
  have hstable : (prefixWord ++ tailWord_3609928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609928).length < 2 ^ (prefixWord ++ tailWord_3609928).sum := by decide
  have hdescent : baseEnd_3609928 < baseStart_3609928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609945 : List Nat := [1, 2, 1, 2, 2, 2, 5, 1, 2, 5]
def baseStart_3609945 : Nat := 118140960795 + 3609945 * 2 ^ 59
def prefixEnd_3609945 : Nat := 4983230072969 + 3 ^ 40 * 3609945 * 2
def baseEnd_3609945 : Nat := 617878973764994602428557

theorem tailTrace_3609945 : CollatzResearch.WordTrace tailWord_3609945 prefixEnd_3609945 617878973764994602428557 := by
  unfold tailWord_3609945
  simp only [CollatzResearch.WordTrace]
  refine ⟨131665510906793269366687289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87777007271195512911124859 131665510906793269366687289)
  ·
    refine ⟨98749133180094952025015467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131665510906793269366687289 98749133180094952025015467)
    ·
      refine ⟨148123699770142428037523201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98749133180094952025015467 148123699770142428037523201)
      ·
        refine ⟨111092774827606821028142401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148123699770142428037523201 111092774827606821028142401)
        ·
          refine ⟨83319581120705115771106801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111092774827606821028142401 83319581120705115771106801)
          ·
            refine ⟨62489685840528836828330101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83319581120705115771106801 62489685840528836828330101)
            ·
              refine ⟨5858408047549578452655947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62489685840528836828330101 5858408047549578452655947)
              ·
                refine ⟨8787612071324367678983921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5858408047549578452655947 8787612071324367678983921)
                ·
                  refine ⟨6590709053493275759237941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8787612071324367678983921 6590709053493275759237941)
                  ·
                    refine ⟨617878973764994602428557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6590709053493275759237941 617878973764994602428557)
                    ·
                      rfl

theorem cell23_3609945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 1, 2, 5].length) (baseStart_3609945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3609945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3609945 prefixEnd_3609945 := by exact prefixLift 3609945
  have htrace : WordTrace (prefixWord ++ tailWord_3609945) baseStart_3609945 baseEnd_3609945 := by
    simpa [prefixWord, tailWord_3609945, baseEnd_3609945] using wordTrace_append hprefix tailTrace_3609945
  have hstable : (prefixWord ++ tailWord_3609945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609945).length < 2 ^ (prefixWord ++ tailWord_3609945).sum := by decide
  have hdescent : baseEnd_3609945 < baseStart_3609945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3609992 : List Nat := [2, 1, 3, 3, 1, 2, 2, 2, 3, 4]
def baseStart_3609992 : Nat := 118140960795 + 3609992 * 2 ^ 59
def prefixEnd_3609992 : Nat := 4983230072969 + 3 ^ 40 * 3609992 * 2
def baseEnd_3609992 : Nat := 617887018295248374465985

theorem tailTrace_3609992 : CollatzResearch.WordTrace tailWord_3609992 prefixEnd_3609992 617887018295248374465985 := by
  unfold tailWord_3609992
  simp only [CollatzResearch.WordTrace]
  refine ⟨65833612568811498196824115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87778150091748664262432153 65833612568811498196824115)
  ·
    refine ⟨98750418853217247295236173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65833612568811498196824115 98750418853217247295236173)
    ·
      refine ⟨37031407069956467735713565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98750418853217247295236173 37031407069956467735713565)
      ·
        refine ⟨13886777651233675400892587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37031407069956467735713565 13886777651233675400892587)
        ·
          refine ⟨20830166476850513101338881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13886777651233675400892587 20830166476850513101338881)
          ·
            refine ⟨15622624857637884826004161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20830166476850513101338881 15622624857637884826004161)
            ·
              refine ⟨11716968643228413619503121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15622624857637884826004161 11716968643228413619503121)
              ·
                refine ⟨8787726482421310214627341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11716968643228413619503121 8787726482421310214627341)
                ·
                  refine ⟨3295397430907991330485253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8787726482421310214627341 3295397430907991330485253)
                  ·
                    refine ⟨617887018295248374465985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3295397430907991330485253 617887018295248374465985)
                    ·
                      rfl

theorem cell23_3609992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 2, 3, 4].length) (baseStart_3609992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3609992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3609992 prefixEnd_3609992 := by exact prefixLift 3609992
  have htrace : WordTrace (prefixWord ++ tailWord_3609992) baseStart_3609992 baseEnd_3609992 := by
    simpa [prefixWord, tailWord_3609992, baseEnd_3609992] using wordTrace_append hprefix tailTrace_3609992
  have hstable : (prefixWord ++ tailWord_3609992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3609992).length < 2 ^ (prefixWord ++ tailWord_3609992).sum := by decide
  have hdescent : baseEnd_3609992 < baseStart_3609992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3609992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610009 : List Nat := [1, 2, 1, 2, 1, 5, 3, 3, 1, 4]
def baseStart_3610009 : Nat := 118140960795 + 3610009 * 2 ^ 59
def prefixEnd_3610009 : Nat := 4983230072969 + 3 ^ 40 * 3610009 * 2
def baseEnd_3610009 : Nat := 617889928018957185628459

theorem tailTrace_3610009 : CollatzResearch.WordTrace tailWord_3610009 prefixEnd_3610009 617889928018957185628459 := by
  unfold tailWord_3610009
  simp only [CollatzResearch.WordTrace]
  refine ⟨131667845178561408297017081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87778563452374272198011387 131667845178561408297017081)
  ·
    refine ⟨98750883883921056222762811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131667845178561408297017081 98750883883921056222762811)
    ·
      refine ⟨148126325825881584334144217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98750883883921056222762811 148126325825881584334144217)
      ·
        refine ⟨111094744369411188250608163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148126325825881584334144217 111094744369411188250608163)
        ·
          refine ⟨166642116554116782375912245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111094744369411188250608163 166642116554116782375912245)
          ·
            refine ⟨15622698426948448347741773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 166642116554116782375912245 15622698426948448347741773)
            ·
              refine ⟨5858511910105668130403165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15622698426948448347741773 5858511910105668130403165)
              ·
                refine ⟨2196941966289625548901187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5858511910105668130403165 2196941966289625548901187)
                ·
                  refine ⟨3295412949434438323351781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2196941966289625548901187 3295412949434438323351781)
                  ·
                    refine ⟨617889928018957185628459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3295412949434438323351781 617889928018957185628459)
                    ·
                      rfl

theorem cell23_3610009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 3, 1, 4].length) (baseStart_3610009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3610009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3610009 prefixEnd_3610009 := by exact prefixLift 3610009
  have htrace : WordTrace (prefixWord ++ tailWord_3610009) baseStart_3610009 baseEnd_3610009 := by
    simpa [prefixWord, tailWord_3610009, baseEnd_3610009] using wordTrace_append hprefix tailTrace_3610009
  have hstable : (prefixWord ++ tailWord_3610009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610009).length < 2 ^ (prefixWord ++ tailWord_3610009).sum := by decide
  have hdescent : baseEnd_3610009 < baseStart_3610009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610032 : List Nat := [2, 1, 1, 1, 2, 1, 1, 7, 3, 1, 3]
def baseStart_3610032 : Nat := 118140960795 + 3610032 * 2 ^ 59
def prefixEnd_3610032 : Nat := 4983230072969 + 3 ^ 40 * 3610032 * 2
def baseEnd_3610032 : Nat := 1853681594111924966897771

theorem tailTrace_3610032 : CollatzResearch.WordTrace tailWord_3610032 prefixEnd_3610032 1853681594111924966897771 := by
  unfold tailWord_3610032
  simp only [CollatzResearch.WordTrace]
  refine ⟨65834342028739041612552175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87779122704985388816736233 65834342028739041612552175)
  ·
    refine ⟨98751513043108562418828263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65834342028739041612552175 98751513043108562418828263)
    ·
      refine ⟨148127269564662843628242395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98751513043108562418828263 148127269564662843628242395)
      ·
        refine ⟨222190904346994265442363593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148127269564662843628242395 222190904346994265442363593)
        ·
          refine ⟨166643178260245699081772695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222190904346994265442363593 166643178260245699081772695)
          ·
            refine ⟨249964767390368548622659043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166643178260245699081772695 249964767390368548622659043)
            ·
              refine ⟨374947151085552822933988565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249964767390368548622659043 374947151085552822933988565)
              ·
                refine ⟨8787823853567644287515357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 374947151085552822933988565 8787823853567644287515357)
                ·
                  refine ⟨3295433945087866607818259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8787823853567644287515357 3295433945087866607818259)
                  ·
                    refine ⟨4943150917631799911727389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3295433945087866607818259 4943150917631799911727389)
                    ·
                      refine ⟨1853681594111924966897771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4943150917631799911727389 1853681594111924966897771)
                      ·
                        rfl

theorem cell23_3610032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7, 3, 1, 3].length) (baseStart_3610032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3610032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3610032 prefixEnd_3610032 := by exact prefixLift 3610032
  have htrace : WordTrace (prefixWord ++ tailWord_3610032) baseStart_3610032 baseEnd_3610032 := by
    simpa [prefixWord, tailWord_3610032, baseEnd_3610032] using wordTrace_append hprefix tailTrace_3610032
  have hstable : (prefixWord ++ tailWord_3610032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610032).length < 2 ^ (prefixWord ++ tailWord_3610032).sum := by decide
  have hdescent : baseEnd_3610032 < baseStart_3610032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610050 : List Nat := [3, 5, 2, 1, 1, 1, 2, 1, 2, 1, 4]
def baseStart_3610050 : Nat := 118140960795 + 3610050 * 2 ^ 59
def prefixEnd_3610050 : Nat := 4983230072969 + 3 ^ 40 * 3610050 * 2
def baseEnd_3610050 : Nat := 1853690836763705896472689

theorem tailTrace_3610050 : CollatzResearch.WordTrace tailWord_3610050 prefixEnd_3610050 1853690836763705896472689 := by
  unfold tailWord_3610050
  simp only [CollatzResearch.WordTrace]
  refine ⟨32917335142853218074814901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87779560380941914866173069 32917335142853218074814901)
  ·
    refine ⟨3086000169642489194513897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32917335142853218074814901 3086000169642489194513897)
    ·
      refine ⟨2314500127231866895885423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3086000169642489194513897 2314500127231866895885423)
      ·
        refine ⟨3471750190847800343828135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2314500127231866895885423 3471750190847800343828135)
        ·
          refine ⟨5207625286271700515742203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3471750190847800343828135 5207625286271700515742203)
          ·
            refine ⟨7811437929407550773613305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5207625286271700515742203 7811437929407550773613305)
            ·
              refine ⟨5858578447055663080209979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7811437929407550773613305 5858578447055663080209979)
              ·
                refine ⟨8787867670583494620314969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5858578447055663080209979 8787867670583494620314969)
                ·
                  refine ⟨6590900752937620965236227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8787867670583494620314969 6590900752937620965236227)
                  ·
                    refine ⟨9886351129406431447854341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6590900752937620965236227 9886351129406431447854341)
                    ·
                      refine ⟨1853690836763705896472689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9886351129406431447854341 1853690836763705896472689)
                      ·
                        rfl

theorem cell23_3610050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_3610050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3610050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3610050 prefixEnd_3610050 := by exact prefixLift 3610050
  have htrace : WordTrace (prefixWord ++ tailWord_3610050) baseStart_3610050 baseEnd_3610050 := by
    simpa [prefixWord, tailWord_3610050, baseEnd_3610050] using wordTrace_append hprefix tailTrace_3610050
  have hstable : (prefixWord ++ tailWord_3610050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610050).length < 2 ^ (prefixWord ++ tailWord_3610050).sum := by decide
  have hdescent : baseEnd_3610050 < baseStart_3610050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610069 : List Nat := [1, 3, 2, 3, 1, 1, 5, 1, 1, 5]
def baseStart_3610069 : Nat := 118140960795 + 3610069 * 2 ^ 59
def prefixEnd_3610069 : Nat := 4983230072969 + 3 ^ 40 * 3610069 * 2
def baseEnd_3610069 : Nat := 617900197632047107378367

theorem tailTrace_3610069 : CollatzResearch.WordTrace tailWord_3610069 prefixEnd_3610069 617900197632047107378367 := by
  unfold tailWord_3610069
  simp only [CollatzResearch.WordTrace]
  refine ⟨131670033558344038544201261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87780022372229359029467507 131670033558344038544201261)
  ·
    refine ⟨49376262584379014454075473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131670033558344038544201261 49376262584379014454075473)
    ·
      refine ⟨37032196938284260840556605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49376262584379014454075473 37032196938284260840556605)
      ·
        refine ⟨13887073851856597815208727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37032196938284260840556605 13887073851856597815208727)
        ·
          refine ⟨20830610777784896722813091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13887073851856597815208727 20830610777784896722813091)
          ·
            refine ⟨31245916166677345084219637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20830610777784896722813091 31245916166677345084219637)
            ·
              refine ⟨2929304640626001101645591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31245916166677345084219637 2929304640626001101645591)
              ·
                refine ⟨4393956960939001652468387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2929304640626001101645591 4393956960939001652468387)
                ·
                  refine ⟨6590935441408502478702581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4393956960939001652468387 6590935441408502478702581)
                  ·
                    refine ⟨617900197632047107378367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6590935441408502478702581 617900197632047107378367)
                    ·
                      rfl

theorem cell23_3610069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5, 1, 1, 5].length) (baseStart_3610069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3610069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3610069 prefixEnd_3610069 := by exact prefixLift 3610069
  have htrace : WordTrace (prefixWord ++ tailWord_3610069) baseStart_3610069 baseEnd_3610069 := by
    simpa [prefixWord, tailWord_3610069, baseEnd_3610069] using wordTrace_append hprefix tailTrace_3610069
  have hstable : (prefixWord ++ tailWord_3610069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610069).length < 2 ^ (prefixWord ++ tailWord_3610069).sum := by decide
  have hdescent : baseEnd_3610069 < baseStart_3610069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610072 : List Nat := [2, 1, 2, 2, 2, 1, 2, 5, 1, 1, 4]
def baseStart_3610072 : Nat := 118140960795 + 3610072 * 2 ^ 59
def prefixEnd_3610072 : Nat := 4983230072969 + 3 ^ 40 * 3610072 * 2
def baseEnd_3610072 : Nat := 1853702133338104810397587

theorem tailTrace_3610072 : CollatzResearch.WordTrace tailWord_3610072 prefixEnd_3610072 1853702133338104810397587 := by
  unfold tailWord_3610072
  simp only [CollatzResearch.WordTrace]
  refine ⟨65835071488666585028280235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87780095318222113371040313 65835071488666585028280235)
  ·
    refine ⟨98752607232999877542420353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65835071488666585028280235 98752607232999877542420353)
    ·
      refine ⟨74064455424749908156815265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98752607232999877542420353 74064455424749908156815265)
      ·
        refine ⟨55548341568562431117611449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74064455424749908156815265 55548341568562431117611449)
        ·
          refine ⟨41661256176421823338208587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55548341568562431117611449 41661256176421823338208587)
          ·
            refine ⟨62491884264632735007312881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41661256176421823338208587 62491884264632735007312881)
            ·
              refine ⟨46868913198474551255484661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62491884264632735007312881 46868913198474551255484661)
              ·
                refine ⟨4393960612356989180201687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46868913198474551255484661 4393960612356989180201687)
                ·
                  refine ⟨6590940918535483770302531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4393960612356989180201687 6590940918535483770302531)
                  ·
                    refine ⟨9886411377803225655453797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6590940918535483770302531 9886411377803225655453797)
                    ·
                      refine ⟨1853702133338104810397587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9886411377803225655453797 1853702133338104810397587)
                      ·
                        rfl

theorem cell23_3610072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 5, 1, 1, 4].length) (baseStart_3610072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3610072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3610072 prefixEnd_3610072 := by exact prefixLift 3610072
  have htrace : WordTrace (prefixWord ++ tailWord_3610072) baseStart_3610072 baseEnd_3610072 := by
    simpa [prefixWord, tailWord_3610072, baseEnd_3610072] using wordTrace_append hprefix tailTrace_3610072
  have hstable : (prefixWord ++ tailWord_3610072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610072).length < 2 ^ (prefixWord ++ tailWord_3610072).sum := by decide
  have hdescent : baseEnd_3610072 < baseStart_3610072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610083 : List Nat := [1, 1, 1, 6, 2, 1, 4, 2, 1, 1, 3]
def baseStart_3610083 : Nat := 118140960795 + 3610083 * 2 ^ 59
def prefixEnd_3610083 : Nat := 4983230072969 + 3 ^ 40 * 3610083 * 2
def baseEnd_3610083 : Nat := 1853707781625304267360037

theorem tailTrace_3610083 : CollatzResearch.WordTrace tailWord_3610083 prefixEnd_3610083 1853707781625304267360037 := by
  unfold tailWord_3610083
  simp only [CollatzResearch.WordTrace]
  refine ⟨131670544180293318935210903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87780362786862212623473935 131670544180293318935210903)
  ·
    refine ⟨197505816270439978402816355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131670544180293318935210903 197505816270439978402816355)
    ·
      refine ⟨296258724405659967604224533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197505816270439978402816355 296258724405659967604224533)
      ·
        refine ⟨13887127706515310981448025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 296258724405659967604224533 13887127706515310981448025)
        ·
          refine ⟨10415345779886483236086019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13887127706515310981448025 10415345779886483236086019)
          ·
            refine ⟨15623018669829724854129029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10415345779886483236086019 15623018669829724854129029)
            ·
              refine ⟨2929316000593073410149193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15623018669829724854129029 2929316000593073410149193)
              ·
                refine ⟨2196987000444805057611895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2929316000593073410149193 2196987000444805057611895)
                ·
                  refine ⟨3295480500667207586417843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2196987000444805057611895 3295480500667207586417843)
                  ·
                    refine ⟨4943220751000811379626765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3295480500667207586417843 4943220751000811379626765)
                    ·
                      refine ⟨1853707781625304267360037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4943220751000811379626765 1853707781625304267360037)
                      ·
                        rfl

theorem cell23_3610083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_3610083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3610083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3610083 prefixEnd_3610083 := by exact prefixLift 3610083
  have htrace : WordTrace (prefixWord ++ tailWord_3610083) baseStart_3610083 baseEnd_3610083 := by
    simpa [prefixWord, tailWord_3610083, baseEnd_3610083] using wordTrace_append hprefix tailTrace_3610083
  have hstable : (prefixWord ++ tailWord_3610083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610083).length < 2 ^ (prefixWord ++ tailWord_3610083).sum := by decide
  have hdescent : baseEnd_3610083 < baseStart_3610083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610095 : List Nat := [1, 1, 2, 1, 4, 1, 5, 8]
def baseStart_3610095 : Nat := 118140960795 + 3610095 * 2 ^ 59
def prefixEnd_3610095 : Nat := 4983230072969 + 3 ^ 40 * 3610095 * 2
def baseEnd_3610095 : Nat := 68656071977524378533703

theorem tailTrace_3610095 : CollatzResearch.WordTrace tailWord_3610095 prefixEnd_3610095 68656071977524378533703 := by
  unfold tailWord_3610095
  simp only [CollatzResearch.WordTrace]
  refine ⟨131670981856249844984647739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87780654570833229989765159 131670981856249844984647739)
  ·
    refine ⟨197506472784374767476971609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131670981856249844984647739 197506472784374767476971609)
    ·
      refine ⟨148129854588281075607728707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197506472784374767476971609 148129854588281075607728707)
      ·
        refine ⟨222194781882421613411593061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148129854588281075607728707 222194781882421613411593061)
        ·
          refine ⟨41661521602954052514673699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 222194781882421613411593061 41661521602954052514673699)
          ·
            refine ⟨62492282404431078772010549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41661521602954052514673699 62492282404431078772010549)
            ·
              refine ⟨5858651475415413634875989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62492282404431078772010549 5858651475415413634875989)
              ·
                refine ⟨68656071977524378533703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5858651475415413634875989 68656071977524378533703)
                ·
                  rfl

theorem cell23_3610095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 8].length) (baseStart_3610095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3610095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3610095 prefixEnd_3610095 := by exact prefixLift 3610095
  have htrace : WordTrace (prefixWord ++ tailWord_3610095) baseStart_3610095 baseEnd_3610095 := by
    simpa [prefixWord, tailWord_3610095, baseEnd_3610095] using wordTrace_append hprefix tailTrace_3610095
  have hstable : (prefixWord ++ tailWord_3610095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610095).length < 2 ^ (prefixWord ++ tailWord_3610095).sum := by decide
  have hdescent : baseEnd_3610095 < baseStart_3610095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610110 : List Nat := [4, 2, 2, 3, 1, 2, 1, 1, 2, 3, 2]
def baseStart_3610110 : Nat := 118140960795 + 3610110 * 2 ^ 59
def prefixEnd_3610110 : Nat := 4983230072969 + 3 ^ 40 * 3610110 * 2
def baseEnd_3610110 : Nat := 1853721645602975661722413

theorem tailTrace_3610110 : CollatzResearch.WordTrace tailWord_3610110 prefixEnd_3610110 1853721645602975661722413 := by
  unfold tailWord_3610110
  simp only [CollatzResearch.WordTrace]
  refine ⟨16458941118899437818305473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87781019300797001697629189 16458941118899437818305473)
  ·
    refine ⟨12344205839174578363729105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16458941118899437818305473 12344205839174578363729105)
    ·
      refine ⟨9258154379380933772796829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12344205839174578363729105 9258154379380933772796829)
      ·
        refine ⟨3471807892267850164798811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9258154379380933772796829 3471807892267850164798811)
        ·
          refine ⟨5207711838401775247198217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3471807892267850164798811 5207711838401775247198217)
          ·
            refine ⟨3905783878801331435398663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5207711838401775247198217 3905783878801331435398663)
            ·
              refine ⟨5858675818201997153097995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3905783878801331435398663 5858675818201997153097995)
              ·
                refine ⟨8788013727302995729646993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5858675818201997153097995 8788013727302995729646993)
                ·
                  refine ⟨6591010295477246797235245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8788013727302995729646993 6591010295477246797235245)
                  ·
                    refine ⟨2471628860803967548963217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6591010295477246797235245 2471628860803967548963217)
                    ·
                      refine ⟨1853721645602975661722413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2471628860803967548963217 1853721645602975661722413)
                      ·
                        rfl

theorem cell23_3610110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_3610110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3610110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3610110 prefixEnd_3610110 := by exact prefixLift 3610110
  have htrace : WordTrace (prefixWord ++ tailWord_3610110) baseStart_3610110 baseEnd_3610110 := by
    simpa [prefixWord, tailWord_3610110, baseEnd_3610110] using wordTrace_append hprefix tailTrace_3610110
  have hstable : (prefixWord ++ tailWord_3610110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610110).length < 2 ^ (prefixWord ++ tailWord_3610110).sum := by decide
  have hdescent : baseEnd_3610110 < baseStart_3610110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610123 : List Nat := [1, 1, 1, 1, 9, 1, 2, 1, 1, 1, 4]
def baseStart_3610123 : Nat := 118140960795 + 3610123 * 2 ^ 59
def prefixEnd_3610123 : Nat := 4983230072969 + 3 ^ 40 * 3610123 * 2
def baseEnd_3610123 : Nat := 1853728320851484110859853

theorem tailTrace_3610123 : CollatzResearch.WordTrace tailWord_3610123 prefixEnd_3610123 1853728320851484110859853 := by
  unfold tailWord_3610123
  simp only [CollatzResearch.WordTrace]
  refine ⟨131672003100148405766667023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87781335400098937177778015 131672003100148405766667023)
  ·
    refine ⟨197508004650222608650000535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131672003100148405766667023 197508004650222608650000535)
    ·
      refine ⟨296262006975333912975000803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197508004650222608650000535 296262006975333912975000803)
      ·
        refine ⟨444393010463000869462501205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296262006975333912975000803 444393010463000869462501205)
        ·
          refine ⟨2603865295681645719506843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 444393010463000869462501205 2603865295681645719506843)
          ·
            refine ⟨3905797943522468579260265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2603865295681645719506843 3905797943522468579260265)
            ·
              refine ⟨2929348457641851434445199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3905797943522468579260265 2929348457641851434445199)
              ·
                refine ⟨4394022686462777151667799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2929348457641851434445199 4394022686462777151667799)
                ·
                  refine ⟨6591034029694165727501699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4394022686462777151667799 6591034029694165727501699)
                  ·
                    refine ⟨9886551044541248591252549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6591034029694165727501699 9886551044541248591252549)
                    ·
                      refine ⟨1853728320851484110859853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9886551044541248591252549 1853728320851484110859853)
                      ·
                        rfl

theorem cell23_3610123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 2, 1, 1, 1, 4].length) (baseStart_3610123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3610123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3610123 prefixEnd_3610123 := by exact prefixLift 3610123
  have htrace : WordTrace (prefixWord ++ tailWord_3610123) baseStart_3610123 baseEnd_3610123 := by
    simpa [prefixWord, tailWord_3610123, baseEnd_3610123] using wordTrace_append hprefix tailTrace_3610123
  have hstable : (prefixWord ++ tailWord_3610123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610123).length < 2 ^ (prefixWord ++ tailWord_3610123).sum := by decide
  have hdescent : baseEnd_3610123 < baseStart_3610123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610126 : List Nat := [4, 1, 1, 2, 4, 1, 1, 3, 1, 2, 3]
def baseStart_3610126 : Nat := 118140960795 + 3610126 * 2 ^ 59
def prefixEnd_3610126 : Nat := 4983230072969 + 3 ^ 40 * 3610126 * 2
def baseEnd_3610126 : Nat := 1853729861293447599122339

theorem tailTrace_3610126 : CollatzResearch.WordTrace tailWord_3610126 prefixEnd_3610126 1853729861293447599122339 := by
  unfold tailWord_3610126
  simp only [CollatzResearch.WordTrace]
  refine ⟨16459014064892192159878279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87781408346091691519350821 16459014064892192159878279)
  ·
    refine ⟨24688521097338288239817419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16459014064892192159878279 24688521097338288239817419)
    ·
      refine ⟨37032781646007432359726129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24688521097338288239817419 37032781646007432359726129)
      ·
        refine ⟨27774586234505574269794597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37032781646007432359726129 27774586234505574269794597)
        ·
          refine ⟨5207734918969795175586487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27774586234505574269794597 5207734918969795175586487)
          ·
            refine ⟨7811602378454692763379731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5207734918969795175586487 7811602378454692763379731)
            ·
              refine ⟨11717403567682039145069597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7811602378454692763379731 11717403567682039145069597)
              ·
                refine ⟨4394026337880764679401099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11717403567682039145069597 4394026337880764679401099)
                ·
                  refine ⟨6591039506821147019101649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4394026337880764679401099 6591039506821147019101649)
                  ·
                    refine ⟨4943279630115860264326237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6591039506821147019101649 4943279630115860264326237)
                    ·
                      refine ⟨1853729861293447599122339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4943279630115860264326237 1853729861293447599122339)
                      ·
                        rfl

theorem cell23_3610126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 3, 1, 2, 3].length) (baseStart_3610126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3610126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3610126 prefixEnd_3610126 := by exact prefixLift 3610126
  have htrace : WordTrace (prefixWord ++ tailWord_3610126) baseStart_3610126 baseEnd_3610126 := by
    simpa [prefixWord, tailWord_3610126, baseEnd_3610126] using wordTrace_append hprefix tailTrace_3610126
  have hstable : (prefixWord ++ tailWord_3610126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610126).length < 2 ^ (prefixWord ++ tailWord_3610126).sum := by decide
  have hdescent : baseEnd_3610126 < baseStart_3610126 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610185 : List Nat := [1, 2, 1, 1, 2, 2, 1, 4, 9]
def baseStart_3610185 : Nat := 118140960795 + 3610185 * 2 ^ 59
def prefixEnd_3610185 : Nat := 4983230072969 + 3 ^ 40 * 3610185 * 2
def baseEnd_3610185 : Nat := 205973350739118096476063

theorem tailTrace_3610185 : CollatzResearch.WordTrace tailWord_3610185 prefixEnd_3610185 205973350739118096476063 := by
  unfold tailWord_3610185
  simp only [CollatzResearch.WordTrace]
  refine ⟨131674264425923790355424009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87782842950615860236949339 131674264425923790355424009)
  ·
    refine ⟨98755698319442842766568007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131674264425923790355424009 98755698319442842766568007)
    ·
      refine ⟨148133547479164264149852011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98755698319442842766568007 148133547479164264149852011)
      ·
        refine ⟨222200321218746396224778017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148133547479164264149852011 222200321218746396224778017)
        ·
          refine ⟨166650240914059797168583513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222200321218746396224778017 166650240914059797168583513)
          ·
            refine ⟨124987680685544847876437635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166650240914059797168583513 124987680685544847876437635)
            ·
              refine ⟨187481521028317271814656453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124987680685544847876437635 187481521028317271814656453)
              ·
                refine ⟨35152785192809488465248085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 187481521028317271814656453 35152785192809488465248085)
                ·
                  refine ⟨205973350739118096476063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 35152785192809488465248085 205973350739118096476063)
                  ·
                    rfl

theorem cell23_3610185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 9].length) (baseStart_3610185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3610185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3610185 prefixEnd_3610185 := by exact prefixLift 3610185
  have htrace : WordTrace (prefixWord ++ tailWord_3610185) baseStart_3610185 baseEnd_3610185 := by
    simpa [prefixWord, tailWord_3610185, baseEnd_3610185] using wordTrace_append hprefix tailTrace_3610185
  have hstable : (prefixWord ++ tailWord_3610185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610185).length < 2 ^ (prefixWord ++ tailWord_3610185).sum := by decide
  have hdescent : baseEnd_3610185 < baseStart_3610185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610196 : List Nat := [2, 4, 1, 1, 1, 2, 1, 3, 4, 2, 2]
def baseStart_3610196 : Nat := 118140960795 + 3610196 * 2 ^ 59
def prefixEnd_3610196 : Nat := 4983230072969 + 3 ^ 40 * 3610196 * 2
def baseEnd_3610196 : Nat := 1853765804939262325247017

theorem tailTrace_3610196 : CollatzResearch.WordTrace tailWord_3610196 prefixEnd_3610196 1853765804939262325247017 := by
  unfold tailWord_3610196
  simp only [CollatzResearch.WordTrace]
  refine ⟨65837332814441969617037221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87783110419255959489382961 65837332814441969617037221)
  ·
    refine ⟨12344499902707869303194479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65837332814441969617037221 12344499902707869303194479)
    ·
      refine ⟨18516749854061803954791719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12344499902707869303194479 18516749854061803954791719)
      ·
        refine ⟨27775124781092705932187579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18516749854061803954791719 27775124781092705932187579)
        ·
          refine ⟨41662687171639058898281369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27775124781092705932187579 41662687171639058898281369)
          ·
            refine ⟨31247015378729294173711027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41662687171639058898281369 31247015378729294173711027)
            ·
              refine ⟨46870523068093941260566541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31247015378729294173711027 46870523068093941260566541)
              ·
                refine ⟨17576446150535227972712453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46870523068093941260566541 17576446150535227972712453)
                ·
                  refine ⟨3295583653225355244883585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17576446150535227972712453 3295583653225355244883585)
                  ·
                    refine ⟨2471687739919016433662689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3295583653225355244883585 2471687739919016433662689)
                    ·
                      refine ⟨1853765804939262325247017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2471687739919016433662689 1853765804939262325247017)
                      ·
                        rfl

theorem cell23_3610196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 4, 2, 2].length) (baseStart_3610196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3610196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3610196 prefixEnd_3610196 := by exact prefixLift 3610196
  have htrace : WordTrace (prefixWord ++ tailWord_3610196) baseStart_3610196 baseEnd_3610196 := by
    simpa [prefixWord, tailWord_3610196, baseEnd_3610196] using wordTrace_append hprefix tailTrace_3610196
  have hstable : (prefixWord ++ tailWord_3610196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610196).length < 2 ^ (prefixWord ++ tailWord_3610196).sum := by decide
  have hdescent : baseEnd_3610196 < baseStart_3610196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610213 : List Nat := [1, 3, 1, 3, 3, 2, 1, 3, 2, 2, 2]
def baseStart_3610213 : Nat := 118140960795 + 3610213 * 2 ^ 59
def prefixEnd_3610213 : Nat := 4983230072969 + 3 ^ 40 * 3610213 * 2
def baseEnd_3610213 : Nat := 1853774534110388758734439

theorem tailTrace_3610213 : CollatzResearch.WordTrace tailWord_3610213 prefixEnd_3610213 1853774534110388758734439 := by
  unfold tailWord_3610213
  simp only [CollatzResearch.WordTrace]
  refine ⟨131675285669822351137443293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87783523779881567424962195 131675285669822351137443293)
  ·
    refine ⟨49378232126183381676541235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131675285669822351137443293 49378232126183381676541235)
    ·
      refine ⟨74067348189275072514811853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49378232126183381676541235 74067348189275072514811853)
      ·
        refine ⟨27775255570978152193054445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74067348189275072514811853 27775255570978152193054445)
        ·
          refine ⟨10415720839116807072395417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27775255570978152193054445 10415720839116807072395417)
          ·
            refine ⟨7811790629337605304296563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10415720839116807072395417 7811790629337605304296563)
            ·
              refine ⟨11717685944006407956444845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7811790629337605304296563 11717685944006407956444845)
              ·
                refine ⟨4394132229002402983666817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11717685944006407956444845 4394132229002402983666817)
                ·
                  refine ⟨3295599171751802237750113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4394132229002402983666817 3295599171751802237750113)
                  ·
                    refine ⟨2471699378813851678312585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3295599171751802237750113 2471699378813851678312585)
                    ·
                      refine ⟨1853774534110388758734439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2471699378813851678312585 1853774534110388758734439)
                      ·
                        rfl

theorem cell23_3610213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 3, 2, 2, 2].length) (baseStart_3610213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3610213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3610213 prefixEnd_3610213 := by exact prefixLift 3610213
  have htrace : WordTrace (prefixWord ++ tailWord_3610213) baseStart_3610213 baseEnd_3610213 := by
    simpa [prefixWord, tailWord_3610213, baseEnd_3610213] using wordTrace_append hprefix tailTrace_3610213
  have hstable : (prefixWord ++ tailWord_3610213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610213).length < 2 ^ (prefixWord ++ tailWord_3610213).sum := by decide
  have hdescent : baseEnd_3610213 < baseStart_3610213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610312 : List Nat := [2, 1, 3, 1, 2, 2, 1, 1, 1, 1, 8]
def baseStart_3610312 : Nat := 118140960795 + 3610312 * 2 ^ 59
def prefixEnd_3610312 : Nat := 4983230072969 + 3 ^ 40 * 3610312 * 2
def baseEnd_3610312 : Nat := 1853825368695183871396483

theorem tailTrace_3610312 : CollatzResearch.WordTrace tailWord_3610312 prefixEnd_3610312 1853825368695183871396483 := by
  unfold tailWord_3610312
  simp only [CollatzResearch.WordTrace]
  refine ⟨65839448248231845522648595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87785930997642460696864793 65839448248231845522648595)
  ·
    refine ⟨98759172372347768283972893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65839448248231845522648595 98759172372347768283972893)
    ·
      refine ⟨37034689639630413106489835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98759172372347768283972893 37034689639630413106489835)
      ·
        refine ⟨55552034459445619659734753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37034689639630413106489835 55552034459445619659734753)
        ·
          refine ⟨41664025844584214744801065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55552034459445619659734753 41664025844584214744801065)
          ·
            refine ⟨31248019383438161058600799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41664025844584214744801065 31248019383438161058600799)
            ·
              refine ⟨46872029075157241587901199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31248019383438161058600799 46872029075157241587901199)
              ·
                refine ⟨70308043612735862381851799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46872029075157241587901199 70308043612735862381851799)
                ·
                  refine ⟨105462065419103793572777699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70308043612735862381851799 105462065419103793572777699)
                  ·
                    refine ⟨158193098128655690359166549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 105462065419103793572777699 158193098128655690359166549)
                    ·
                      refine ⟨1853825368695183871396483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 158193098128655690359166549 1853825368695183871396483)
                      ·
                        rfl

theorem cell23_3610312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_3610312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3610312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3610312 prefixEnd_3610312 := by exact prefixLift 3610312
  have htrace : WordTrace (prefixWord ++ tailWord_3610312) baseStart_3610312 baseEnd_3610312 := by
    simpa [prefixWord, tailWord_3610312, baseEnd_3610312] using wordTrace_append hprefix tailTrace_3610312
  have hstable : (prefixWord ++ tailWord_3610312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610312).length < 2 ^ (prefixWord ++ tailWord_3610312).sum := by decide
  have hdescent : baseEnd_3610312 < baseStart_3610312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610336 : List Nat := [2, 1, 1, 3, 1, 2, 4, 2, 3, 1, 3]
def baseStart_3610336 : Nat := 118140960795 + 3610336 * 2 ^ 59
def prefixEnd_3610336 : Nat := 4983230072969 + 3 ^ 40 * 3610336 * 2
def baseEnd_3610336 : Nat := 1853837692230891777496373

theorem tailTrace_3610336 : CollatzResearch.WordTrace tailWord_3610336 prefixEnd_3610336 1853837692230891777496373 := by
  unfold tailWord_3610336
  simp only [CollatzResearch.WordTrace]
  refine ⟨65839885924188371572085431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87786514565584495429447241 65839885924188371572085431)
  ·
    refine ⟨98759828886282557358128147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65839885924188371572085431 98759828886282557358128147)
    ·
      refine ⟨148139743329423836037192221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98759828886282557358128147 148139743329423836037192221)
      ·
        refine ⟨55552403748533938513947083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148139743329423836037192221 55552403748533938513947083)
        ·
          refine ⟨83328605622800907770920625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55552403748533938513947083 83328605622800907770920625)
          ·
            refine ⟨62496454217100680828190469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83328605622800907770920625 62496454217100680828190469)
            ·
              refine ⟨11718085165706377655285713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62496454217100680828190469 11718085165706377655285713)
              ·
                refine ⟨8788563874279783241464285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11718085165706377655285713 8788563874279783241464285)
                ·
                  refine ⟨3295711452854918715549107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8788563874279783241464285 3295711452854918715549107)
                  ·
                    refine ⟨4943567179282378073323661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3295711452854918715549107 4943567179282378073323661)
                    ·
                      refine ⟨1853837692230891777496373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4943567179282378073323661 1853837692230891777496373)
                      ·
                        rfl

theorem cell23_3610336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 2, 3, 1, 3].length) (baseStart_3610336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3610336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3610336 prefixEnd_3610336 := by exact prefixLift 3610336
  have htrace : WordTrace (prefixWord ++ tailWord_3610336) baseStart_3610336 baseEnd_3610336 := by
    simpa [prefixWord, tailWord_3610336, baseEnd_3610336] using wordTrace_append hprefix tailTrace_3610336
  have hstable : (prefixWord ++ tailWord_3610336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610336).length < 2 ^ (prefixWord ++ tailWord_3610336).sum := by decide
  have hdescent : baseEnd_3610336 < baseStart_3610336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610346 : List Nat := [3, 1, 3, 1, 1, 1, 4, 1, 1, 5, 2]
def baseStart_3610346 : Nat := 118140960795 + 3610346 * 2 ^ 59
def prefixEnd_3610346 : Nat := 4983230072969 + 3 ^ 40 * 3610346 * 2
def baseEnd_3610346 : Nat := 1853842827037436738371327

theorem tailTrace_3610346 : CollatzResearch.WordTrace tailWord_3610346 prefixEnd_3610346 1853842827037436738371327 := by
  unfold tailWord_3610346
  simp only [CollatzResearch.WordTrace]
  refine ⟨32920034144585128713008723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87786757718893676568023261 32920034144585128713008723)
  ·
    refine ⟨49380051216877693069513085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32920034144585128713008723 49380051216877693069513085)
    ·
      refine ⟨18517519206329134901067407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49380051216877693069513085 18517519206329134901067407)
      ·
        refine ⟨27776278809493702351601111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18517519206329134901067407 27776278809493702351601111)
        ·
          refine ⟨41664418214240553527401667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27776278809493702351601111 41664418214240553527401667)
          ·
            refine ⟨62496627321360830291102501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41664418214240553527401667 62496627321360830291102501)
            ·
              refine ⟨11718117622755155679581719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62496627321360830291102501 11718117622755155679581719)
              ·
                refine ⟨17577176434132733519372579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11718117622755155679581719 17577176434132733519372579)
                ·
                  refine ⟨26365764651199100279058869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17577176434132733519372579 26365764651199100279058869)
                  ·
                    refine ⟨2471790436049915651161769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26365764651199100279058869 2471790436049915651161769)
                    ·
                      refine ⟨1853842827037436738371327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2471790436049915651161769 1853842827037436738371327)
                      ·
                        rfl

theorem cell23_3610346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 1, 5, 2].length) (baseStart_3610346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3610346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3610346 prefixEnd_3610346 := by exact prefixLift 3610346
  have htrace : WordTrace (prefixWord ++ tailWord_3610346) baseStart_3610346 baseEnd_3610346 := by
    simpa [prefixWord, tailWord_3610346, baseEnd_3610346] using wordTrace_append hprefix tailTrace_3610346
  have hstable : (prefixWord ++ tailWord_3610346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610346).length < 2 ^ (prefixWord ++ tailWord_3610346).sum := by decide
  have hdescent : baseEnd_3610346 < baseStart_3610346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610379 : List Nat := [1, 1, 1, 1, 5, 1, 4, 2, 1, 1, 5]
def baseStart_3610379 : Nat := 118140960795 + 3610379 * 2 ^ 59
def prefixEnd_3610379 : Nat := 4983230072969 + 3 ^ 40 * 3610379 * 2
def baseEnd_3610379 : Nat := 1853859771899035109258675

theorem tailTrace_3610379 : CollatzResearch.WordTrace tailWord_3610379 prefixEnd_3610379 1853859771899035109258675 := by
  unfold tailWord_3610379
  simp only [CollatzResearch.WordTrace]
  refine ⟨131681340187220961487986191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87787560124813974325324127 131681340187220961487986191)
  ·
    refine ⟨197522010280831442231979287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131681340187220961487986191 197522010280831442231979287)
    ·
      refine ⟨296283015421247163347968931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197522010280831442231979287 296283015421247163347968931)
      ·
        refine ⟨444424523131870745021953397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296283015421247163347968931 444424523131870745021953397)
        ·
          refine ⟨41664799043612882345808131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 444424523131870745021953397 41664799043612882345808131)
          ·
            refine ⟨62497198565419323518712197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41664799043612882345808131 62497198565419323518712197)
            ·
              refine ⟨11718224731016123159758537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62497198565419323518712197 11718224731016123159758537)
              ·
                refine ⟨8788668548262092369818903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11718224731016123159758537 8788668548262092369818903)
                ·
                  refine ⟨13183002822393138554728355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8788668548262092369818903 13183002822393138554728355)
                  ·
                    refine ⟨19774504233589707832092533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13183002822393138554728355 19774504233589707832092533)
                    ·
                      refine ⟨1853859771899035109258675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19774504233589707832092533 1853859771899035109258675)
                      ·
                        rfl

theorem cell23_3610379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 2, 1, 1, 5].length) (baseStart_3610379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3610379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3610379 prefixEnd_3610379 := by exact prefixLift 3610379
  have htrace : WordTrace (prefixWord ++ tailWord_3610379) baseStart_3610379 baseEnd_3610379 := by
    simpa [prefixWord, tailWord_3610379, baseEnd_3610379] using wordTrace_append hprefix tailTrace_3610379
  have hstable : (prefixWord ++ tailWord_3610379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610379).length < 2 ^ (prefixWord ++ tailWord_3610379).sum := by decide
  have hdescent : baseEnd_3610379 < baseStart_3610379 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610389 : List Nat := [1, 3, 2, 1, 2, 3, 2, 1, 1, 1, 6]
def baseStart_3610389 : Nat := 118140960795 + 3610389 * 2 ^ 59
def prefixEnd_3610389 : Nat := 4983230072969 + 3 ^ 40 * 3610389 * 2
def baseEnd_3610389 : Nat := 1853864906705580070133629

theorem tailTrace_3610389 : CollatzResearch.WordTrace tailWord_3610389 prefixEnd_3610389 1853864906705580070133629 := by
  unfold tailWord_3610389
  simp only [CollatzResearch.WordTrace]
  refine ⟨131681704917184733195850221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87787803278123155463900147 131681704917184733195850221)
  ·
    refine ⟨49380639343944274948443833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131681704917184733195850221 49380639343944274948443833)
    ·
      refine ⟨37035479507958206211332875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49380639343944274948443833 37035479507958206211332875)
      ·
        refine ⟨55553219261937309316999313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37035479507958206211332875 55553219261937309316999313)
        ·
          refine ⟨41664914446452981987749485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55553219261937309316999313 41664914446452981987749485)
          ·
            refine ⟨15624342917419868245406057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41664914446452981987749485 15624342917419868245406057)
            ·
              refine ⟨11718257188064901184054543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15624342917419868245406057 11718257188064901184054543)
              ·
                refine ⟨17577385782097351776081815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11718257188064901184054543 17577385782097351776081815)
                ·
                  refine ⟨26366078673146027664122723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17577385782097351776081815 26366078673146027664122723)
                  ·
                    refine ⟨39549118009719041496184085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26366078673146027664122723 39549118009719041496184085)
                    ·
                      refine ⟨1853864906705580070133629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39549118009719041496184085 1853864906705580070133629)
                      ·
                        rfl

theorem cell23_3610389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_3610389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3610389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3610389 prefixEnd_3610389 := by exact prefixLift 3610389
  have htrace : WordTrace (prefixWord ++ tailWord_3610389) baseStart_3610389 baseEnd_3610389 := by
    simpa [prefixWord, tailWord_3610389, baseEnd_3610389] using wordTrace_append hprefix tailTrace_3610389
  have hstable : (prefixWord ++ tailWord_3610389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610389).length < 2 ^ (prefixWord ++ tailWord_3610389).sum := by decide
  have hdescent : baseEnd_3610389 < baseStart_3610389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610396 : List Nat := [2, 2, 3, 1, 1, 2, 3, 1, 3, 2, 3]
def baseStart_3610396 : Nat := 118140960795 + 3610396 * 2 ^ 59
def prefixEnd_3610396 : Nat := 4983230072969 + 3 ^ 40 * 3610396 * 2
def baseEnd_3610396 : Nat := 1853868501070161542746097

theorem tailTrace_3610396 : CollatzResearch.WordTrace tailWord_3610396 prefixEnd_3610396 1853868501070161542746097 := by
  unfold tailWord_3610396
  simp only [CollatzResearch.WordTrace]
  refine ⟨65840980114079686695677521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87787973485439582260903361 65840980114079686695677521)
  ·
    refine ⟨49380735085559765021758141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65840980114079686695677521 49380735085559765021758141)
    ·
      refine ⟨18517775657084911883159303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49380735085559765021758141 18517775657084911883159303)
      ·
        refine ⟨27776663485627367824738955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18517775657084911883159303 27776663485627367824738955)
        ·
          refine ⟨41664995228441051737108433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27776663485627367824738955 41664995228441051737108433)
          ·
            refine ⟨31248746421330788802831325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41664995228441051737108433 31248746421330788802831325)
            ·
              refine ⟨11718279907999045801061747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31248746421330788802831325 11718279907999045801061747)
              ·
                refine ⟨17577419861998568701592621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11718279907999045801061747 17577419861998568701592621)
                ·
                  refine ⟨6591532448249463263097233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17577419861998568701592621 6591532448249463263097233)
                  ·
                    refine ⟨4943649336187097447322925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6591532448249463263097233 4943649336187097447322925)
                    ·
                      refine ⟨1853868501070161542746097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4943649336187097447322925 1853868501070161542746097)
                      ·
                        rfl

theorem cell23_3610396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_3610396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3610396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3610396 prefixEnd_3610396 := by exact prefixLift 3610396
  have htrace : WordTrace (prefixWord ++ tailWord_3610396) baseStart_3610396 baseEnd_3610396 := by
    simpa [prefixWord, tailWord_3610396, baseEnd_3610396] using wordTrace_append hprefix tailTrace_3610396
  have hstable : (prefixWord ++ tailWord_3610396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610396).length < 2 ^ (prefixWord ++ tailWord_3610396).sum := by decide
  have hdescent : baseEnd_3610396 < baseStart_3610396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610420 : List Nat := [2, 5, 1, 1, 2, 2, 2, 2, 2, 4]
def baseStart_3610420 : Nat := 118140960795 + 3610420 * 2 ^ 59
def prefixEnd_3610420 : Nat := 4983230072969 + 3 ^ 40 * 3610420 * 2
def baseEnd_3610420 : Nat := 617960274868623149615329

theorem tailTrace_3610420 : CollatzResearch.WordTrace tailWord_3610420 prefixEnd_3610420 617960274868623149615329 := by
  unfold tailWord_3610420
  simp only [CollatzResearch.WordTrace]
  refine ⟨65841417790036212745114357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87788557053381616993485809 65841417790036212745114357)
  ·
    refine ⟨6172632917815894944854471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65841417790036212745114357 6172632917815894944854471)
    ·
      refine ⟨9258949376723842417281707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6172632917815894944854471 9258949376723842417281707)
      ·
        refine ⟨13888424065085763625922561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9258949376723842417281707 13888424065085763625922561)
        ·
          refine ⟨10416318048814322719441921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13888424065085763625922561 10416318048814322719441921)
          ·
            refine ⟨7812238536610742039581441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10416318048814322719441921 7812238536610742039581441)
            ·
              refine ⟨5859178902458056529686081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7812238536610742039581441 5859178902458056529686081)
              ·
                refine ⟨4394384176843542397264561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5859178902458056529686081 4394384176843542397264561)
                ·
                  refine ⟨3295788132632656797948421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4394384176843542397264561 3295788132632656797948421)
                  ·
                    refine ⟨617960274868623149615329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3295788132632656797948421 617960274868623149615329)
                    ·
                      rfl

theorem cell23_3610420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_3610420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3610420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3610420 prefixEnd_3610420 := by exact prefixLift 3610420
  have htrace : WordTrace (prefixWord ++ tailWord_3610420) baseStart_3610420 baseEnd_3610420 := by
    simpa [prefixWord, tailWord_3610420, baseEnd_3610420] using wordTrace_append hprefix tailTrace_3610420
  have hstable : (prefixWord ++ tailWord_3610420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610420).length < 2 ^ (prefixWord ++ tailWord_3610420).sum := by decide
  have hdescent : baseEnd_3610420 < baseStart_3610420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610453 : List Nat := [1, 3, 2, 2, 2, 2, 2, 1, 3, 3, 2]
def baseStart_3610453 : Nat := 118140960795 + 3610453 * 2 ^ 59
def prefixEnd_3610453 : Nat := 4983230072969 + 3 ^ 40 * 3610453 * 2
def baseEnd_3610453 : Nat := 1853897769467467819733335

theorem tailTrace_3610453 : CollatzResearch.WordTrace tailWord_3610453 prefixEnd_3610453 1853897769467467819733335 := by
  unfold tailWord_3610453
  simp only [CollatzResearch.WordTrace]
  refine ⟨131684039188952872126180013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87789359459301914750786675 131684039188952872126180013)
  ·
    refine ⟨49381514695857327047317505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131684039188952872126180013 49381514695857327047317505)
    ·
      refine ⟨37036136021892995285488129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49381514695857327047317505 37036136021892995285488129)
      ·
        refine ⟨27777102016419746464116097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37036136021892995285488129 27777102016419746464116097)
        ·
          refine ⟨20832826512314809848087073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27777102016419746464116097 20832826512314809848087073)
          ·
            refine ⟨15624619884236107386065305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20832826512314809848087073 15624619884236107386065305)
            ·
              refine ⟨11718464913177080539548979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15624619884236107386065305 11718464913177080539548979)
              ·
                refine ⟨17577697369765620809323469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11718464913177080539548979 17577697369765620809323469)
                ·
                  refine ⟨6591636513662107803496301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17577697369765620809323469 6591636513662107803496301)
                  ·
                    refine ⟨2471863692623290426311113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6591636513662107803496301 2471863692623290426311113)
                    ·
                      refine ⟨1853897769467467819733335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2471863692623290426311113 1853897769467467819733335)
                      ·
                        rfl

theorem cell23_3610453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 3, 3, 2].length) (baseStart_3610453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3610453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3610453 prefixEnd_3610453 := by exact prefixLift 3610453
  have htrace : WordTrace (prefixWord ++ tailWord_3610453) baseStart_3610453 baseEnd_3610453 := by
    simpa [prefixWord, tailWord_3610453, baseEnd_3610453] using wordTrace_append hprefix tailTrace_3610453
  have hstable : (prefixWord ++ tailWord_3610453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610453).length < 2 ^ (prefixWord ++ tailWord_3610453).sum := by decide
  have hdescent : baseEnd_3610453 < baseStart_3610453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610469 : List Nat := [1, 3, 1, 3, 1, 1, 1, 3, 1, 3, 5]
def baseStart_3610469 : Nat := 118140960795 + 3610469 * 2 ^ 59
def prefixEnd_3610469 : Nat := 4983230072969 + 3 ^ 40 * 3610469 * 2
def baseEnd_3610469 : Nat := 1853905985157939757133261

theorem tailTrace_3610469 : CollatzResearch.WordTrace tailWord_3610469 prefixEnd_3610469 1853905985157939757133261 := by
  unfold tailWord_3610469
  simp only [CollatzResearch.WordTrace]
  refine ⟨131684622756894906858762461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87789748504596604572508307 131684622756894906858762461)
  ·
    refine ⟨49381733533835590072035923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131684622756894906858762461 49381733533835590072035923)
    ·
      refine ⟨74072600300753385108053885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49381733533835590072035923 74072600300753385108053885)
      ·
        refine ⟨27777225112782519415520207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74072600300753385108053885 27777225112782519415520207)
        ·
          refine ⟨41665837669173779123280311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27777225112782519415520207 41665837669173779123280311)
          ·
            refine ⟨62498756503760668684920467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41665837669173779123280311 62498756503760668684920467)
            ·
              refine ⟨93748134755641003027380701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62498756503760668684920467 93748134755641003027380701)
              ·
                refine ⟨35155550533365376135267763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93748134755641003027380701 35155550533365376135267763)
                ·
                  refine ⟨52733325800048064202901645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35155550533365376135267763 52733325800048064202901645)
                  ·
                    refine ⟨19774997175018024076088117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52733325800048064202901645 19774997175018024076088117)
                    ·
                      refine ⟨1853905985157939757133261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19774997175018024076088117 1853905985157939757133261)
                      ·
                        rfl

theorem cell23_3610469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_3610469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3610469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3610469 prefixEnd_3610469 := by exact prefixLift 3610469
  have htrace : WordTrace (prefixWord ++ tailWord_3610469) baseStart_3610469 baseEnd_3610469 := by
    simpa [prefixWord, tailWord_3610469, baseEnd_3610469] using wordTrace_append hprefix tailTrace_3610469
  have hstable : (prefixWord ++ tailWord_3610469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610469).length < 2 ^ (prefixWord ++ tailWord_3610469).sum := by decide
  have hdescent : baseEnd_3610469 < baseStart_3610469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610494 : List Nat := [4, 2, 3, 1, 1, 2, 3, 1, 2, 1, 3]
def baseStart_3610494 : Nat := 118140960795 + 3610494 * 2 ^ 59
def prefixEnd_3610494 : Nat := 4983230072969 + 3 ^ 40 * 3610494 * 2
def baseEnd_3610494 : Nat := 1853918822174302159320647

theorem tailTrace_3610494 : CollatzResearch.WordTrace tailWord_3610494 prefixEnd_3610494 1853918822174302159320647 := by
  unfold tailWord_3610494
  simp only [CollatzResearch.WordTrace]
  refine ⟨16460691822725542016052817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87790356387869557418948357 16460691822725542016052817)
  ·
    refine ⟨12345518867044156512039613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16460691822725542016052817 12345518867044156512039613)
    ·
      refine ⟨4629569575141558692014855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12345518867044156512039613 4629569575141558692014855)
      ·
        refine ⟨6944354362712338038022283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4629569575141558692014855 6944354362712338038022283)
        ·
          refine ⟨10416531544068507057033425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6944354362712338038022283 10416531544068507057033425)
          ·
            refine ⟨7812398658051380292775069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10416531544068507057033425 7812398658051380292775069)
            ·
              refine ⟨2929649496769267609790651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7812398658051380292775069 2929649496769267609790651)
              ·
                refine ⟨4394474245153901414685977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2929649496769267609790651 4394474245153901414685977)
                ·
                  refine ⟨3295855683865426061014483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4394474245153901414685977 3295855683865426061014483)
                  ·
                    refine ⟨4943783525798139091521725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3295855683865426061014483 4943783525798139091521725)
                    ·
                      refine ⟨1853918822174302159320647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4943783525798139091521725 1853918822174302159320647)
                      ·
                        rfl

theorem cell23_3610494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_3610494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3610494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3610494 prefixEnd_3610494 := by exact prefixLift 3610494
  have htrace : WordTrace (prefixWord ++ tailWord_3610494) baseStart_3610494 baseEnd_3610494 := by
    simpa [prefixWord, tailWord_3610494, baseEnd_3610494] using wordTrace_append hprefix tailTrace_3610494
  have hstable : (prefixWord ++ tailWord_3610494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610494).length < 2 ^ (prefixWord ++ tailWord_3610494).sum := by decide
  have hdescent : baseEnd_3610494 < baseStart_3610494 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610500 : List Nat := [2, 3, 2, 1, 1, 1, 2, 5, 2, 2, 2]
def baseStart_3610500 : Nat := 118140960795 + 3610500 * 2 ^ 59
def prefixEnd_3610500 : Nat := 4983230072969 + 3 ^ 40 * 3610500 * 2
def baseEnd_3610500 : Nat := 1853921903058229135845619

theorem tailTrace_3610500 : CollatzResearch.WordTrace tailWord_3610500 prefixEnd_3610500 1853921903058229135845619 := by
  unfold tailWord_3610500
  simp only [CollatzResearch.WordTrace]
  refine ⟨65842876709891299576570477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87790502279855066102093969 65842876709891299576570477)
  ·
    refine ⟨24691078766209237341213929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65842876709891299576570477 24691078766209237341213929)
    ·
      refine ⟨18518309074656928005910447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24691078766209237341213929 18518309074656928005910447)
      ·
        refine ⟨27777463611985392008865671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18518309074656928005910447 27777463611985392008865671)
        ·
          refine ⟨41666195417978088013298507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27777463611985392008865671 41666195417978088013298507)
          ·
            refine ⟨62499293126967132019947761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41666195417978088013298507 62499293126967132019947761)
            ·
              refine ⟨46874469845225349014960821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62499293126967132019947761 46874469845225349014960821)
              ·
                refine ⟨4394481547989876470152577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46874469845225349014960821 4394481547989876470152577)
                ·
                  refine ⟨3295861160992407352614433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4394481547989876470152577 3295861160992407352614433)
                  ·
                    refine ⟨2471895870744305514460825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3295861160992407352614433 2471895870744305514460825)
                    ·
                      refine ⟨1853921903058229135845619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2471895870744305514460825 1853921903058229135845619)
                      ·
                        rfl

theorem cell23_3610500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 5, 2, 2, 2].length) (baseStart_3610500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3610500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3610500 prefixEnd_3610500 := by exact prefixLift 3610500
  have htrace : WordTrace (prefixWord ++ tailWord_3610500) baseStart_3610500 baseEnd_3610500 := by
    simpa [prefixWord, tailWord_3610500, baseEnd_3610500] using wordTrace_append hprefix tailTrace_3610500
  have hstable : (prefixWord ++ tailWord_3610500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610500).length < 2 ^ (prefixWord ++ tailWord_3610500).sum := by decide
  have hdescent : baseEnd_3610500 < baseStart_3610500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610576 : List Nat := [2, 1, 1, 1, 1, 2, 4, 3, 1, 4, 3]
def baseStart_3610576 : Nat := 118140960795 + 3610576 * 2 ^ 59
def prefixEnd_3610576 : Nat := 4983230072969 + 3 ^ 40 * 3610576 * 2
def baseEnd_3610576 : Nat := 1853960927587970838495269

theorem tailTrace_3610576 : CollatzResearch.WordTrace tailWord_3610576 prefixEnd_3610576 1853960927587970838495269 := by
  unfold tailWord_3610576
  simp only [CollatzResearch.WordTrace]
  refine ⟨65844262683753632066453791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87792350245004842755271721 65844262683753632066453791)
  ·
    refine ⟨98766394025630448099680687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65844262683753632066453791 98766394025630448099680687)
    ·
      refine ⟨148149591038445672149521031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98766394025630448099680687 148149591038445672149521031)
      ·
        refine ⟨222224386557668508224281547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148149591038445672149521031 222224386557668508224281547)
        ·
          refine ⟨333336579836502762336422321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222224386557668508224281547 333336579836502762336422321)
          ·
            refine ⟨250002434877377071752316741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 333336579836502762336422321 250002434877377071752316741)
            ·
              refine ⟨46875456539508200953559389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 250002434877377071752316741 46875456539508200953559389)
              ·
                refine ⟨17578296202315575357584771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46875456539508200953559389 17578296202315575357584771)
                ·
                  refine ⟨26367444303473363036377157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17578296202315575357584771 26367444303473363036377157)
                  ·
                    refine ⟨4943895806901255569320717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26367444303473363036377157 4943895806901255569320717)
                    ·
                      refine ⟨1853960927587970838495269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4943895806901255569320717 1853960927587970838495269)
                      ·
                        rfl

theorem cell23_3610576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4, 3].length) (baseStart_3610576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3610576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3610576 prefixEnd_3610576 := by exact prefixLift 3610576
  have htrace : WordTrace (prefixWord ++ tailWord_3610576) baseStart_3610576 baseEnd_3610576 := by
    simpa [prefixWord, tailWord_3610576, baseEnd_3610576] using wordTrace_append hprefix tailTrace_3610576
  have hstable : (prefixWord ++ tailWord_3610576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610576).length < 2 ^ (prefixWord ++ tailWord_3610576).sum := by decide
  have hdescent : baseEnd_3610576 < baseStart_3610576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610593 : List Nat := [1, 2, 3, 1, 2, 1, 4, 2, 2, 2, 3]
def baseStart_3610593 : Nat := 118140960795 + 3610593 * 2 ^ 59
def prefixEnd_3610593 : Nat := 4983230072969 + 3 ^ 40 * 3610593 * 2
def baseEnd_3610593 : Nat := 1853969656759097271982691

theorem tailTrace_3610593 : CollatzResearch.WordTrace tailWord_3610593 prefixEnd_3610593 1853969656759097271982691 := by
  unfold tailWord_3610593
  simp only [CollatzResearch.WordTrace]
  refine ⟨131689145408445676036276433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87792763605630450690850955 131689145408445676036276433)
  ·
    refine ⟨98766859056334257027207325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131689145408445676036276433 98766859056334257027207325)
    ·
      refine ⟨37037572146125346385202747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98766859056334257027207325 37037572146125346385202747)
      ·
        refine ⟨55556358219188019577804121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37037572146125346385202747 55556358219188019577804121)
        ·
          refine ⟨41667268664391014683353091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55556358219188019577804121 41667268664391014683353091)
          ·
            refine ⟨62500902996586522025029637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41667268664391014683353091 62500902996586522025029637)
            ·
              refine ⟨11718919311859972879693057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62500902996586522025029637 11718919311859972879693057)
              ·
                refine ⟨8789189483894979659769793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11718919311859972879693057 8789189483894979659769793)
                ·
                  refine ⟨6591892112921234744827345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8789189483894979659769793 6591892112921234744827345)
                  ·
                    refine ⟨4943919084690926058620509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6591892112921234744827345 4943919084690926058620509)
                    ·
                      refine ⟨1853969656759097271982691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4943919084690926058620509 1853969656759097271982691)
                      ·
                        rfl

theorem cell23_3610593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 2, 2, 2, 3].length) (baseStart_3610593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3610593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3610593 prefixEnd_3610593 := by exact prefixLift 3610593
  have htrace : WordTrace (prefixWord ++ tailWord_3610593) baseStart_3610593 baseEnd_3610593 := by
    simpa [prefixWord, tailWord_3610593, baseEnd_3610593] using wordTrace_append hprefix tailTrace_3610593
  have hstable : (prefixWord ++ tailWord_3610593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610593).length < 2 ^ (prefixWord ++ tailWord_3610593).sum := by decide
  have hdescent : baseEnd_3610593 < baseStart_3610593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610647 : List Nat := [1, 1, 3, 5, 3, 1, 1, 2, 6]
def baseStart_3610647 : Nat := 118140960795 + 3610647 * 2 ^ 59
def prefixEnd_3610647 : Nat := 4983230072969 + 3 ^ 40 * 3610647 * 2
def baseEnd_3610647 : Nat := 205999709412715562300827

theorem tailTrace_3610647 : CollatzResearch.WordTrace tailWord_3610647 prefixEnd_3610647 205999709412715562300827 := by
  unfold tailWord_3610647
  simp only [CollatzResearch.WordTrace]
  refine ⟨131691114950250043258742195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87794076633500028839161463 131691114950250043258742195)
  ·
    refine ⟨197536672425375064888113293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131691114950250043258742195 197536672425375064888113293)
    ·
      refine ⟨74076252159515649333042485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197536672425375064888113293 74076252159515649333042485)
      ·
        refine ⟨6944648639954592124972733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74076252159515649333042485 6944648639954592124972733)
        ·
          refine ⟨2604243239982972046864775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6944648639954592124972733 2604243239982972046864775)
          ·
            refine ⟨3906364859974458070297163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2604243239982972046864775 3906364859974458070297163)
            ·
              refine ⟨5859547289961687105445745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3906364859974458070297163 5859547289961687105445745)
              ·
                refine ⟨4394660467471265329084309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5859547289961687105445745 4394660467471265329084309)
                ·
                  refine ⟨205999709412715562300827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4394660467471265329084309 205999709412715562300827)
                  ·
                    rfl

theorem cell23_3610647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 2, 6].length) (baseStart_3610647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3610647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3610647 prefixEnd_3610647 := by exact prefixLift 3610647
  have htrace : WordTrace (prefixWord ++ tailWord_3610647) baseStart_3610647 baseEnd_3610647 := by
    simpa [prefixWord, tailWord_3610647, baseEnd_3610647] using wordTrace_append hprefix tailTrace_3610647
  have hstable : (prefixWord ++ tailWord_3610647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610647).length < 2 ^ (prefixWord ++ tailWord_3610647).sum := by decide
  have hdescent : baseEnd_3610647 < baseStart_3610647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610657 : List Nat := [1, 2, 3, 2, 4, 1, 2, 1, 3, 1, 3]
def baseStart_3610657 : Nat := 118140960795 + 3610657 * 2 ^ 59
def prefixEnd_3610657 : Nat := 4983230072969 + 3 ^ 40 * 3610657 * 2
def baseEnd_3610657 : Nat := 1854002519520985021582397

theorem tailTrace_3610657 : CollatzResearch.WordTrace tailWord_3610657 prefixEnd_3610657 1854002519520985021582397 := by
  unfold tailWord_3610657
  simp only [CollatzResearch.WordTrace]
  refine ⟨131691479680213814966606225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87794319786809209977737483 131691479680213814966606225)
  ·
    refine ⟨98768609760160361224954669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131691479680213814966606225 98768609760160361224954669)
    ·
      refine ⟨37038228660060135459358001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98768609760160361224954669 37038228660060135459358001)
      ·
        refine ⟨27778671495045101594518501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37038228660060135459358001 27778671495045101594518501)
        ·
          refine ⟨5208500905320956548972219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27778671495045101594518501 5208500905320956548972219)
          ·
            refine ⟨7812751357981434823458329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5208500905320956548972219 7812751357981434823458329)
            ·
              refine ⟨5859563518486076117593747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7812751357981434823458329 5859563518486076117593747)
              ·
                refine ⟨8789345277729114176390621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5859563518486076117593747 8789345277729114176390621)
                ·
                  refine ⟨3296004479148417816146483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8789345277729114176390621 3296004479148417816146483)
                  ·
                    refine ⟨4944006718722626724219725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3296004479148417816146483 4944006718722626724219725)
                    ·
                      refine ⟨1854002519520985021582397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4944006718722626724219725 1854002519520985021582397)
                      ·
                        rfl

theorem cell23_3610657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 1, 3, 1, 3].length) (baseStart_3610657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3610657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3610657 prefixEnd_3610657 := by exact prefixLift 3610657
  have htrace : WordTrace (prefixWord ++ tailWord_3610657) baseStart_3610657 baseEnd_3610657 := by
    simpa [prefixWord, tailWord_3610657, baseEnd_3610657] using wordTrace_append hprefix tailTrace_3610657
  have hstable : (prefixWord ++ tailWord_3610657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610657).length < 2 ^ (prefixWord ++ tailWord_3610657).sum := by decide
  have hdescent : baseEnd_3610657 < baseStart_3610657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610673 : List Nat := [1, 2, 2, 3, 1, 3, 3, 1, 1, 6]
def baseStart_3610673 : Nat := 118140960795 + 3610673 * 2 ^ 59
def prefixEnd_3610673 : Nat := 4983230072969 + 3 ^ 40 * 3610673 * 2
def baseEnd_3610673 : Nat := 618003578403818986327441

theorem tailTrace_3610673 : CollatzResearch.WordTrace tailWord_3610673 prefixEnd_3610673 618003578403818986327441 := by
  unfold tailWord_3610673
  simp only [CollatzResearch.WordTrace]
  refine ⟨131692063248155849699188673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87794708832103899799459115 131692063248155849699188673)
  ·
    refine ⟨98769047436116887274391505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131692063248155849699188673 98769047436116887274391505)
    ·
      refine ⟨74076785577087665455793629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98769047436116887274391505 74076785577087665455793629)
      ·
        refine ⟨27778794591407874545922611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74076785577087665455793629 27778794591407874545922611)
        ·
          refine ⟨41668191887111811818883917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27778794591407874545922611 41668191887111811818883917)
          ·
            refine ⟨15625571957666929432081469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41668191887111811818883917 15625571957666929432081469)
            ·
              refine ⟨5859589484125098537030551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15625571957666929432081469 5859589484125098537030551)
              ·
                refine ⟨8789384226187647805545827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5859589484125098537030551 8789384226187647805545827)
                ·
                  refine ⟨13184076339281471708318741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8789384226187647805545827 13184076339281471708318741)
                  ·
                    refine ⟨618003578403818986327441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13184076339281471708318741 618003578403818986327441)
                    ·
                      rfl

theorem cell23_3610673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 1, 1, 6].length) (baseStart_3610673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3610673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3610673 prefixEnd_3610673 := by exact prefixLift 3610673
  have htrace : WordTrace (prefixWord ++ tailWord_3610673) baseStart_3610673 baseEnd_3610673 := by
    simpa [prefixWord, tailWord_3610673, baseEnd_3610673] using wordTrace_append hprefix tailTrace_3610673
  have hstable : (prefixWord ++ tailWord_3610673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610673).length < 2 ^ (prefixWord ++ tailWord_3610673).sum := by decide
  have hdescent : baseEnd_3610673 < baseStart_3610673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610700 : List Nat := [2, 2, 1, 3, 1, 1, 4, 3, 1, 2, 3]
def baseStart_3610700 : Nat := 118140960795 + 3610700 * 2 ^ 59
def prefixEnd_3610700 : Nat := 4983230072969 + 3 ^ 40 * 3610700 * 2
def baseEnd_3610700 : Nat := 1854024599189128353344699

theorem tailTrace_3610700 : CollatzResearch.WordTrace tailWord_3610700 prefixEnd_3610700 1854024599189128353344699 := by
  unfold tailWord_3610700
  simp only [CollatzResearch.WordTrace]
  refine ⟨65846524009529016655210777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87795365346038688873614369 65846524009529016655210777)
  ·
    refine ⟨49384893007146762491408083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65846524009529016655210777 49384893007146762491408083)
    ·
      refine ⟨74077339510720143737112125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49384893007146762491408083 74077339510720143737112125)
      ·
        refine ⟨27779002316520053901417047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74077339510720143737112125 27779002316520053901417047)
        ·
          refine ⟨41668503474780080852125571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27779002316520053901417047 41668503474780080852125571)
          ·
            refine ⟨62502755212170121278188357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41668503474780080852125571 62502755212170121278188357)
            ·
              refine ⟨11719266602281897739660317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62502755212170121278188357 11719266602281897739660317)
              ·
                refine ⟨4394724975855711652372619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11719266602281897739660317 4394724975855711652372619)
                ·
                  refine ⟨6592087463783567478558929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4394724975855711652372619 6592087463783567478558929)
                  ·
                    refine ⟨4944065597837675608919197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6592087463783567478558929 4944065597837675608919197)
                    ·
                      refine ⟨1854024599189128353344699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4944065597837675608919197 1854024599189128353344699)
                      ·
                        rfl

theorem cell23_3610700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 3, 1, 2, 3].length) (baseStart_3610700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3610700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3610700 prefixEnd_3610700 := by exact prefixLift 3610700
  have htrace : WordTrace (prefixWord ++ tailWord_3610700) baseStart_3610700 baseEnd_3610700 := by
    simpa [prefixWord, tailWord_3610700, baseEnd_3610700] using wordTrace_append hprefix tailTrace_3610700
  have hstable : (prefixWord ++ tailWord_3610700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610700).length < 2 ^ (prefixWord ++ tailWord_3610700).sum := by decide
  have hdescent : baseEnd_3610700 < baseStart_3610700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610773 : List Nat := [1, 3, 2, 1, 1, 1, 3, 1, 1, 6, 3]
def baseStart_3610773 : Nat := 118140960795 + 3610773 * 2 ^ 59
def prefixEnd_3610773 : Nat := 4983230072969 + 3 ^ 40 * 3610773 * 2
def baseEnd_3610773 : Nat := 1854062083276906567731863

theorem tailTrace_3610773 : CollatzResearch.WordTrace tailWord_3610773 prefixEnd_3610773 1854062083276906567731863 := by
  unfold tailWord_3610773
  simp only [CollatzResearch.WordTrace]
  refine ⟨131695710547793566777828973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87797140365195711185219315 131695710547793566777828973)
  ·
    refine ⟨49385891455422587541685865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131695710547793566777828973 49385891455422587541685865)
    ·
      refine ⟨37039418591566940656264399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49385891455422587541685865 37039418591566940656264399)
      ·
        refine ⟨55559127887350410984396599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37039418591566940656264399 55559127887350410984396599)
        ·
          refine ⟨83338691831025616476594899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55559127887350410984396599 83338691831025616476594899)
          ·
            refine ⟨125008037746538424714892349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83338691831025616476594899 125008037746538424714892349)
            ·
              refine ⟨46878014154951909268084631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125008037746538424714892349 46878014154951909268084631)
              ·
                refine ⟨70317021232427863902126947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46878014154951909268084631 70317021232427863902126947)
                ·
                  refine ⟨105475531848641795853190421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70317021232427863902126947 105475531848641795853190421)
                  ·
                    refine ⟨4944165555405084180618301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 105475531848641795853190421 4944165555405084180618301)
                    ·
                      refine ⟨1854062083276906567731863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4944165555405084180618301 1854062083276906567731863)
                      ·
                        rfl

theorem cell23_3610773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 6, 3].length) (baseStart_3610773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3610773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3610773 prefixEnd_3610773 := by exact prefixLift 3610773
  have htrace : WordTrace (prefixWord ++ tailWord_3610773) baseStart_3610773 baseEnd_3610773 := by
    simpa [prefixWord, tailWord_3610773, baseEnd_3610773] using wordTrace_append hprefix tailTrace_3610773
  have hstable : (prefixWord ++ tailWord_3610773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610773).length < 2 ^ (prefixWord ++ tailWord_3610773).sum := by decide
  have hdescent : baseEnd_3610773 < baseStart_3610773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610803 : List Nat := [1, 1, 1, 2, 3, 2, 1, 1, 3, 5, 3]
def baseStart_3610803 : Nat := 118140960795 + 3610803 * 2 ^ 59
def prefixEnd_3610803 : Nat := 4983230072969 + 3 ^ 40 * 3610803 * 2
def baseEnd_3610803 : Nat := 1854077487696541450356725

theorem tailTrace_3610803 : CollatzResearch.WordTrace tailWord_3610803 prefixEnd_3610803 1854077487696541450356725 := by
  unfold tailWord_3610803
  simp only [CollatzResearch.WordTrace]
  refine ⟨131696804737684881901421063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87797869825123254600947375 131696804737684881901421063)
  ·
    refine ⟨197545207106527322852131595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131696804737684881901421063 197545207106527322852131595)
    ·
      refine ⟨296317810659790984278197393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197545207106527322852131595 296317810659790984278197393)
      ·
        refine ⟨222238357994843238208648045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296317810659790984278197393 222238357994843238208648045)
        ·
          refine ⟨83339384248066214328243017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222238357994843238208648045 83339384248066214328243017)
          ·
            refine ⟨62504538186049660746182263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83339384248066214328243017 62504538186049660746182263)
            ·
              refine ⟨93756807279074491119273395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62504538186049660746182263 93756807279074491119273395)
              ·
                refine ⟨140635210918611736678910093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93756807279074491119273395 140635210918611736678910093)
                ·
                  refine ⟨52738204094479401254591285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 140635210918611736678910093 52738204094479401254591285)
                  ·
                    refine ⟨4944206633857443867617933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52738204094479401254591285 4944206633857443867617933)
                    ·
                      refine ⟨1854077487696541450356725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4944206633857443867617933 1854077487696541450356725)
                      ·
                        rfl

theorem cell23_3610803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 5, 3].length) (baseStart_3610803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3610803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3610803 prefixEnd_3610803 := by exact prefixLift 3610803
  have htrace : WordTrace (prefixWord ++ tailWord_3610803) baseStart_3610803 baseEnd_3610803 := by
    simpa [prefixWord, tailWord_3610803, baseEnd_3610803] using wordTrace_append hprefix tailTrace_3610803
  have hstable : (prefixWord ++ tailWord_3610803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610803).length < 2 ^ (prefixWord ++ tailWord_3610803).sum := by decide
  have hdescent : baseEnd_3610803 < baseStart_3610803 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610810 : List Nat := [3, 1, 1, 1, 2, 2, 3, 5, 5]
def baseStart_3610810 : Nat := 118140960795 + 3610810 * 2 ^ 59
def prefixEnd_3610810 : Nat := 4983230072969 + 3 ^ 40 * 3610810 * 2
def baseEnd_3610810 : Nat := 206009009117902546996577

theorem tailTrace_3610810 : CollatzResearch.WordTrace tailWord_3610810 prefixEnd_3610810 206009009117902546996577 := by
  unfold tailWord_3610810
  simp only [CollatzResearch.WordTrace]
  refine ⟨32924265012164880524231471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87798040032439681397950589 32924265012164880524231471)
  ·
    refine ⟨49386397518247320786347207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32924265012164880524231471 49386397518247320786347207)
    ·
      refine ⟨74079596277370981179520811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49386397518247320786347207 74079596277370981179520811)
      ·
        refine ⟨111119394416056471769281217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74079596277370981179520811 111119394416056471769281217)
        ·
          refine ⟨83339545812042353826960913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111119394416056471769281217 83339545812042353826960913)
          ·
            refine ⟨62504659359031765370220685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83339545812042353826960913 62504659359031765370220685)
            ·
              refine ⟨23439247259636912013832757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62504659359031765370220685 23439247259636912013832757)
              ·
                refine ⟨2197429430590960501296821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23439247259636912013832757 2197429430590960501296821)
                ·
                  refine ⟨206009009117902546996577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2197429430590960501296821 206009009117902546996577)
                  ·
                    rfl

theorem cell23_3610810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 5, 5].length) (baseStart_3610810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3610810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3610810 prefixEnd_3610810 := by exact prefixLift 3610810
  have htrace : WordTrace (prefixWord ++ tailWord_3610810) baseStart_3610810 baseEnd_3610810 := by
    simpa [prefixWord, tailWord_3610810, baseEnd_3610810] using wordTrace_append hprefix tailTrace_3610810
  have hstable : (prefixWord ++ tailWord_3610810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610810).length < 2 ^ (prefixWord ++ tailWord_3610810).sum := by decide
  have hdescent : baseEnd_3610810 < baseStart_3610810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610833 : List Nat := [1, 2, 2, 1, 2, 2, 2, 3, 1, 2, 5]
def baseStart_3610833 : Nat := 118140960795 + 3610833 * 2 ^ 59
def prefixEnd_3610833 : Nat := 4983230072969 + 3 ^ 40 * 3610833 * 2
def baseEnd_3610833 : Nat := 1854092892116176332981587

theorem tailTrace_3610833 : CollatzResearch.WordTrace tailWord_3610833 prefixEnd_3610833 1854092892116176332981587 := by
  unfold tailWord_3610833
  simp only [CollatzResearch.WordTrace]
  refine ⟨131697898927576197025013153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87798599285050798016675435 131697898927576197025013153)
  ·
    refine ⟨98773424195682147768759865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131697898927576197025013153 98773424195682147768759865)
    ·
      refine ⟨74080068146761610826569899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98773424195682147768759865 74080068146761610826569899)
      ·
        refine ⟨111120102220142416239854849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74080068146761610826569899 111120102220142416239854849)
        ·
          refine ⟨83340076665106812179891137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111120102220142416239854849 83340076665106812179891137)
          ·
            refine ⟨62505057498830109134918353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83340076665106812179891137 62505057498830109134918353)
            ·
              refine ⟨46878793124122581851188765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62505057498830109134918353 46878793124122581851188765)
              ·
                refine ⟨17579547421545968194195787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46878793124122581851188765 17579547421545968194195787)
                ·
                  refine ⟨26369321132318952291293681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17579547421545968194195787 26369321132318952291293681)
                  ·
                    refine ⟨19776990849239214218470261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26369321132318952291293681 19776990849239214218470261)
                    ·
                      refine ⟨1854092892116176332981587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19776990849239214218470261 1854092892116176332981587)
                      ·
                        rfl

theorem cell23_3610833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 2, 5].length) (baseStart_3610833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3610833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3610833 prefixEnd_3610833 := by exact prefixLift 3610833
  have htrace : WordTrace (prefixWord ++ tailWord_3610833) baseStart_3610833 baseEnd_3610833 := by
    simpa [prefixWord, tailWord_3610833, baseEnd_3610833] using wordTrace_append hprefix tailTrace_3610833
  have hstable : (prefixWord ++ tailWord_3610833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610833).length < 2 ^ (prefixWord ++ tailWord_3610833).sum := by decide
  have hdescent : baseEnd_3610833 < baseStart_3610833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610843 : List Nat := [1, 1, 1, 1, 1, 1, 1, 8, 1, 3, 4]
def baseStart_3610843 : Nat := 118140960795 + 3610843 * 2 ^ 59
def prefixEnd_3610843 : Nat := 4983230072969 + 3 ^ 40 * 3610843 * 2
def baseEnd_3610843 : Nat := 1854098026922721293856541

theorem tailTrace_3610843 : CollatzResearch.WordTrace tailWord_3610843 prefixEnd_3610843 1854098026922721293856541 := by
  unfold tailWord_3610843
  simp only [CollatzResearch.WordTrace]
  refine ⟨131698263657539968732877183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87798842438359979155251455 131698263657539968732877183)
  ·
    refine ⟨197547395486309953099315775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131698263657539968732877183 197547395486309953099315775)
    ·
      refine ⟨296321093229464929648973663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197547395486309953099315775 296321093229464929648973663)
      ·
        refine ⟨444481639844197394473460495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296321093229464929648973663 444481639844197394473460495)
        ·
          refine ⟨666722459766296091710190743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444481639844197394473460495 666722459766296091710190743)
          ·
            refine ⟨1000083689649444137565286115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 666722459766296091710190743 1000083689649444137565286115)
            ·
              refine ⟨1500125534474166206347929173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1000083689649444137565286115 1500125534474166206347929173)
              ·
                refine ⟨17579596107119135230639795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1500125534474166206347929173 17579596107119135230639795)
                ·
                  refine ⟨26369394160678702845959693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17579596107119135230639795 26369394160678702845959693)
                  ·
                    refine ⟨9888522810254513567234885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26369394160678702845959693 9888522810254513567234885)
                    ·
                      refine ⟨1854098026922721293856541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9888522810254513567234885 1854098026922721293856541)
                      ·
                        rfl

theorem cell23_3610843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 3, 4].length) (baseStart_3610843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3610843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3610843 prefixEnd_3610843 := by exact prefixLift 3610843
  have htrace : WordTrace (prefixWord ++ tailWord_3610843) baseStart_3610843 baseEnd_3610843 := by
    simpa [prefixWord, tailWord_3610843, baseEnd_3610843] using wordTrace_append hprefix tailTrace_3610843
  have hstable : (prefixWord ++ tailWord_3610843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610843).length < 2 ^ (prefixWord ++ tailWord_3610843).sum := by decide
  have hdescent : baseEnd_3610843 < baseStart_3610843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610860 : List Nat := [2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 4]
def baseStart_3610860 : Nat := 118140960795 + 3610860 * 2 ^ 59
def prefixEnd_3610860 : Nat := 4983230072969 + 3 ^ 40 * 3610860 * 2
def baseEnd_3610860 : Nat := 1854106756093847727343963

theorem tailTrace_3610860 : CollatzResearch.WordTrace tailWord_3610860 prefixEnd_3610860 1854106756093847727343963 := by
  unfold tailWord_3610860
  simp only [CollatzResearch.WordTrace]
  refine ⟨65849441849239190318123017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87799255798985587090830689 65849441849239190318123017)
  ·
    refine ⟨49387081386929392738592263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65849441849239190318123017 49387081386929392738592263)
    ·
      refine ⟨74080622080394089107888395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49387081386929392738592263 74080622080394089107888395)
      ·
        refine ⟨111120933120591133661832593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74080622080394089107888395 111120933120591133661832593)
        ·
          refine ⟨83340699840443350246374445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111120933120591133661832593 83340699840443350246374445)
          ·
            refine ⟨31252762440166256342390417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83340699840443350246374445 31252762440166256342390417)
            ·
              refine ⟨23439571830124692256792813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31252762440166256342390417 23439571830124692256792813)
              ·
                refine ⟨8789839436296759596297305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23439571830124692256792813 8789839436296759596297305)
                ·
                  refine ⟨6592379577222569697222979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8789839436296759596297305 6592379577222569697222979)
                  ·
                    refine ⟨9888569365833854545834469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6592379577222569697222979 9888569365833854545834469)
                    ·
                      refine ⟨1854106756093847727343963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9888569365833854545834469 1854106756093847727343963)
                      ·
                        rfl

theorem cell23_3610860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 4].length) (baseStart_3610860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3610860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3610860 prefixEnd_3610860 := by exact prefixLift 3610860
  have htrace : WordTrace (prefixWord ++ tailWord_3610860) baseStart_3610860 baseEnd_3610860 := by
    simpa [prefixWord, tailWord_3610860, baseEnd_3610860] using wordTrace_append hprefix tailTrace_3610860
  have hstable : (prefixWord ++ tailWord_3610860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610860).length < 2 ^ (prefixWord ++ tailWord_3610860).sum := by decide
  have hdescent : baseEnd_3610860 < baseStart_3610860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610861 : List Nat := [1, 5, 1, 2, 4, 1, 1, 3, 5]
def baseStart_3610861 : Nat := 118140960795 + 3610861 * 2 ^ 59
def prefixEnd_3610861 : Nat := 4983230072969 + 3 ^ 40 * 3610861 * 2
def baseEnd_3610861 : Nat := 206011918841611358159051

theorem tailTrace_3610861 : CollatzResearch.WordTrace tailWord_3610861 prefixEnd_3610861 206011918841611358159051 := by
  unfold tailWord_3610861
  simp only [CollatzResearch.WordTrace]
  refine ⟨131698920171474757807032437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87799280114316505204688291 131698920171474757807032437)
  ·
    refine ⟨12346773766075758544409291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 131698920171474757807032437 12346773766075758544409291)
    ·
      refine ⟨18520160649113637816613937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12346773766075758544409291 18520160649113637816613937)
      ·
        refine ⟨13890120486835228362460453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18520160649113637816613937 13890120486835228362460453)
        ·
          refine ⟨2604397591281605317961335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13890120486835228362460453 2604397591281605317961335)
          ·
            refine ⟨3906596386922407976942003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2604397591281605317961335 3906596386922407976942003)
            ·
              refine ⟨5859894580383611965413005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3906596386922407976942003 5859894580383611965413005)
              ·
                refine ⟨2197460467643854487029877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5859894580383611965413005 2197460467643854487029877)
                ·
                  refine ⟨206011918841611358159051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2197460467643854487029877 206011918841611358159051)
                  ·
                    rfl

theorem cell23_3610861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 3, 5].length) (baseStart_3610861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3610861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3610861 prefixEnd_3610861 := by exact prefixLift 3610861
  have htrace : WordTrace (prefixWord ++ tailWord_3610861) baseStart_3610861 baseEnd_3610861 := by
    simpa [prefixWord, tailWord_3610861, baseEnd_3610861] using wordTrace_append hprefix tailTrace_3610861
  have hstable : (prefixWord ++ tailWord_3610861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610861).length < 2 ^ (prefixWord ++ tailWord_3610861).sum := by decide
  have hdescent : baseEnd_3610861 < baseStart_3610861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610873 : List Nat := [1, 2, 1, 3, 1, 1, 2, 3, 2, 1, 6]
def baseStart_3610873 : Nat := 118140960795 + 3610873 * 2 ^ 59
def prefixEnd_3610873 : Nat := 4983230072969 + 3 ^ 40 * 3610873 * 2
def baseEnd_3610873 : Nat := 1854113431342356176481403

theorem tailTrace_3610873 : CollatzResearch.WordTrace tailWord_3610873 prefixEnd_3610873 1854113431342356176481403 := by
  unfold tailWord_3610873
  simp only [CollatzResearch.WordTrace]
  refine ⟨131699357847431283856469273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87799571898287522570979515 131699357847431283856469273)
  ·
    refine ⟨98774518385573462892351955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131699357847431283856469273 98774518385573462892351955)
    ·
      refine ⟨148161777578360194338527933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98774518385573462892351955 148161777578360194338527933)
      ·
        refine ⟨55560666591885072876947975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148161777578360194338527933 55560666591885072876947975)
        ·
          refine ⟨83340999887827609315421963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55560666591885072876947975 83340999887827609315421963)
          ·
            refine ⟨125011499831741413973132945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83340999887827609315421963 125011499831741413973132945)
            ·
              refine ⟨93758624873806060479849709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125011499831741413973132945 93758624873806060479849709)
              ·
                refine ⟨35159484327677272679943641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93758624873806060479849709 35159484327677272679943641)
                ·
                  refine ⟨26369613245757954509957731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35159484327677272679943641 26369613245757954509957731)
                  ·
                    refine ⟨39554419868636931764936597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26369613245757954509957731 39554419868636931764936597)
                    ·
                      refine ⟨1854113431342356176481403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39554419868636931764936597 1854113431342356176481403)
                      ·
                        rfl

theorem cell23_3610873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_3610873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3610873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3610873 prefixEnd_3610873 := by exact prefixLift 3610873
  have htrace : WordTrace (prefixWord ++ tailWord_3610873) baseStart_3610873 baseEnd_3610873 := by
    simpa [prefixWord, tailWord_3610873, baseEnd_3610873] using wordTrace_append hprefix tailTrace_3610873
  have hstable : (prefixWord ++ tailWord_3610873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610873).length < 2 ^ (prefixWord ++ tailWord_3610873).sum := by decide
  have hdescent : baseEnd_3610873 < baseStart_3610873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610880 : List Nat := [2, 1, 1, 2, 1, 1, 5, 1, 4, 2, 3]
def baseStart_3610880 : Nat := 118140960795 + 3610880 * 2 ^ 59
def prefixEnd_3610880 : Nat := 4983230072969 + 3 ^ 40 * 3610880 * 2
def baseEnd_3610880 : Nat := 1854117025706937649093871

theorem tailTrace_3610880 : CollatzResearch.WordTrace tailWord_3610880 prefixEnd_3610880 1854117025706937649093871 := by
  unfold tailWord_3610880
  simp only [CollatzResearch.WordTrace]
  refine ⟨65849806579202962025987047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87799742105603949367982729 65849806579202962025987047)
  ·
    refine ⟨98774709868804443038980571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65849806579202962025987047 98774709868804443038980571)
    ·
      refine ⟨148162064803206664558470857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98774709868804443038980571 148162064803206664558470857)
      ·
        refine ⟨111121548602404998418853143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148162064803206664558470857 111121548602404998418853143)
        ·
          refine ⟨166682322903607497628279715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111121548602404998418853143 166682322903607497628279715)
          ·
            refine ⟨250023484355411246442419573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166682322903607497628279715 250023484355411246442419573)
            ·
              refine ⟨23439701658319804353976835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 250023484355411246442419573 23439701658319804353976835)
              ·
                refine ⟨35159552487479706530965253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23439701658319804353976835 35159552487479706530965253)
                ·
                  refine ⟨6592416091402444974555985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35159552487479706530965253 6592416091402444974555985)
                  ·
                    refine ⟨4944312068551833730916989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6592416091402444974555985 4944312068551833730916989)
                    ·
                      refine ⟨1854117025706937649093871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4944312068551833730916989 1854117025706937649093871)
                      ·
                        rfl

theorem cell23_3610880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2, 3].length) (baseStart_3610880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3610880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3610880 prefixEnd_3610880 := by exact prefixLift 3610880
  have htrace : WordTrace (prefixWord ++ tailWord_3610880) baseStart_3610880 baseEnd_3610880 := by
    simpa [prefixWord, tailWord_3610880, baseEnd_3610880] using wordTrace_append hprefix tailTrace_3610880
  have hstable : (prefixWord ++ tailWord_3610880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610880).length < 2 ^ (prefixWord ++ tailWord_3610880).sum := by decide
  have hdescent : baseEnd_3610880 < baseStart_3610880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610883 : List Nat := [1, 1, 1, 3, 2, 3, 1, 3, 8]
def baseStart_3610883 : Nat := 118140960795 + 3610883 * 2 ^ 59
def prefixEnd_3610883 : Nat := 4983230072969 + 3 ^ 40 * 3610883 * 2
def baseEnd_3610883 : Nat := 206013174016544570817373

theorem tailTrace_3610883 : CollatzResearch.WordTrace tailWord_3610883 prefixEnd_3610883 206013174016544570817373 := by
  unfold tailWord_3610883
  simp only [CollatzResearch.WordTrace]
  refine ⟨131699722577395055564333303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87799815051596703709555535 131699722577395055564333303)
  ·
    refine ⟨197549583866092583346499955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131699722577395055564333303 197549583866092583346499955)
    ·
      refine ⟨296324375799138875019749933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197549583866092583346499955 296324375799138875019749933)
      ·
        refine ⟨111121640924677078132406225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 296324375799138875019749933 111121640924677078132406225)
        ·
          refine ⟨83341230693507808599304669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111121640924677078132406225 83341230693507808599304669)
          ·
            refine ⟨31252961510065428224739251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83341230693507808599304669 31252961510065428224739251)
            ·
              refine ⟨46879442265098142337108877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31252961510065428224739251 46879442265098142337108877)
              ·
                refine ⟨17579790849411803376415829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46879442265098142337108877 17579790849411803376415829)
                ·
                  refine ⟨206013174016544570817373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17579790849411803376415829 206013174016544570817373)
                  ·
                    rfl

theorem cell23_3610883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 8].length) (baseStart_3610883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3610883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3610883 prefixEnd_3610883 := by exact prefixLift 3610883
  have htrace : WordTrace (prefixWord ++ tailWord_3610883) baseStart_3610883 baseEnd_3610883 := by
    simpa [prefixWord, tailWord_3610883, baseEnd_3610883] using wordTrace_append hprefix tailTrace_3610883
  have hstable : (prefixWord ++ tailWord_3610883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610883).length < 2 ^ (prefixWord ++ tailWord_3610883).sum := by decide
  have hdescent : baseEnd_3610883 < baseStart_3610883 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610914 : List Nat := [3, 3, 1, 1, 3, 2, 2, 1, 2, 2, 3]
def baseStart_3610914 : Nat := 118140960795 + 3610914 * 2 ^ 59
def prefixEnd_3610914 : Nat := 4983230072969 + 3 ^ 40 * 3610914 * 2
def baseEnd_3610914 : Nat := 1854134484049190516068715

theorem tailTrace_3610914 : CollatzResearch.WordTrace tailWord_3610914 prefixEnd_3610914 1854134484049190516068715 := by
  unfold tailWord_3610914
  simp only [CollatzResearch.WordTrace]
  refine ⟨32925213310070686964677949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87800568826855165239141197 32925213310070686964677949)
  ·
    refine ⟨12346954991276507611754231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32925213310070686964677949 12346954991276507611754231)
    ·
      refine ⟨18520432486914761417631347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12346954991276507611754231 18520432486914761417631347)
      ·
        refine ⟨27780648730372142126447021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18520432486914761417631347 27780648730372142126447021)
        ·
          refine ⟨10417743273889553297417633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27780648730372142126447021 10417743273889553297417633)
          ·
            refine ⟨7813307455417164973063225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10417743273889553297417633 7813307455417164973063225)
            ·
              refine ⟨5859980591562873729797419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7813307455417164973063225 5859980591562873729797419)
              ·
                refine ⟨8789970887344310594696129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5859980591562873729797419 8789970887344310594696129)
                ·
                  refine ⟨6592478165508232946022097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8789970887344310594696129 6592478165508232946022097)
                  ·
                    refine ⟨4944358624131174709516573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6592478165508232946022097 4944358624131174709516573)
                    ·
                      refine ⟨1854134484049190516068715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4944358624131174709516573 1854134484049190516068715)
                      ·
                        rfl

theorem cell23_3610914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_3610914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3610914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3610914 prefixEnd_3610914 := by exact prefixLift 3610914
  have htrace : WordTrace (prefixWord ++ tailWord_3610914) baseStart_3610914 baseEnd_3610914 := by
    simpa [prefixWord, tailWord_3610914, baseEnd_3610914] using wordTrace_append hprefix tailTrace_3610914
  have hstable : (prefixWord ++ tailWord_3610914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610914).length < 2 ^ (prefixWord ++ tailWord_3610914).sum := by decide
  have hdescent : baseEnd_3610914 < baseStart_3610914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610960 : List Nat := [2, 1, 1, 1, 1, 6, 1, 3, 1, 6]
def baseStart_3610960 : Nat := 118140960795 + 3610960 * 2 ^ 59
def prefixEnd_3610960 : Nat := 4983230072969 + 3 ^ 40 * 3610960 * 2
def baseEnd_3610960 : Nat := 618052701386432445364501

theorem tailTrace_3610960 : CollatzResearch.WordTrace tailWord_3610960 prefixEnd_3610960 618052701386432445364501 := by
  unfold tailWord_3610960
  simp only [CollatzResearch.WordTrace]
  refine ⟨65851265499058048857443167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87801687332077398476590889 65851265499058048857443167)
  ·
    refine ⟨98776898248587073286164751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65851265499058048857443167 98776898248587073286164751)
    ·
      refine ⟨148165347372880609929247127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98776898248587073286164751 148165347372880609929247127)
      ·
        refine ⟨222248021059320914893870691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148165347372880609929247127 222248021059320914893870691)
        ·
          refine ⟨333372031588981372340806037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222248021059320914893870691 333372031588981372340806037)
          ·
            refine ⟨15626813980733501828475283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 333372031588981372340806037 15626813980733501828475283)
            ·
              refine ⟨23440220971100252742712925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15626813980733501828475283 23440220971100252742712925)
              ·
                refine ⟨8790082864162594778517347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23440220971100252742712925 8790082864162594778517347)
                ·
                  refine ⟨13185124296243892167776021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8790082864162594778517347 13185124296243892167776021)
                  ·
                    refine ⟨618052701386432445364501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13185124296243892167776021 618052701386432445364501)
                    ·
                      rfl

theorem cell23_3610960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 3, 1, 6].length) (baseStart_3610960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3610960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3610960 prefixEnd_3610960 := by exact prefixLift 3610960
  have htrace : WordTrace (prefixWord ++ tailWord_3610960) baseStart_3610960 baseEnd_3610960 := by
    simpa [prefixWord, tailWord_3610960, baseEnd_3610960] using wordTrace_append hprefix tailTrace_3610960
  have hstable : (prefixWord ++ tailWord_3610960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610960).length < 2 ^ (prefixWord ++ tailWord_3610960).sum := by decide
  have hdescent : baseEnd_3610960 < baseStart_3610960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610967 : List Nat := [1, 1, 3, 2, 3, 1, 2, 4, 1, 1, 4]
def baseStart_3610967 : Nat := 118140960795 + 3610967 * 2 ^ 59
def prefixEnd_3610967 : Nat := 4983230072969 + 3 ^ 40 * 3610967 * 2
def baseEnd_3610967 : Nat := 1854161698523878808705971

theorem tailTrace_3610967 : CollatzResearch.WordTrace tailWord_3610967 prefixEnd_3610967 1854161698523878808705971 := by
  unfold tailWord_3610967
  simp only [CollatzResearch.WordTrace]
  refine ⟨131702786309090737910391155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87801857539393825273594103 131702786309090737910391155)
  ·
    refine ⟨197554179463636106865586733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131702786309090737910391155 197554179463636106865586733)
    ·
      refine ⟨74082817298863540074595025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197554179463636106865586733 74082817298863540074595025)
      ·
        refine ⟨55562112974147655055946269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74082817298863540074595025 55562112974147655055946269)
        ·
          refine ⟨20835792365305370645979851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55562112974147655055946269 20835792365305370645979851)
          ·
            refine ⟨31253688547958055968969777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20835792365305370645979851 31253688547958055968969777)
            ·
              refine ⟨23440266410968541976727333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31253688547958055968969777 23440266410968541976727333)
              ·
                refine ⟨4395049952056601620636375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23440266410968541976727333 4395049952056601620636375)
                ·
                  refine ⟨6592574928084902430954563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4395049952056601620636375 6592574928084902430954563)
                  ·
                    refine ⟨9888862392127353646431845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6592574928084902430954563 9888862392127353646431845)
                    ·
                      refine ⟨1854161698523878808705971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9888862392127353646431845 1854161698523878808705971)
                      ·
                        rfl

theorem cell23_3610967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 4, 1, 1, 4].length) (baseStart_3610967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3610967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3610967 prefixEnd_3610967 := by exact prefixLift 3610967
  have htrace : WordTrace (prefixWord ++ tailWord_3610967) baseStart_3610967 baseEnd_3610967 := by
    simpa [prefixWord, tailWord_3610967, baseEnd_3610967] using wordTrace_append hprefix tailTrace_3610967
  have hstable : (prefixWord ++ tailWord_3610967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610967).length < 2 ^ (prefixWord ++ tailWord_3610967).sum := by decide
  have hdescent : baseEnd_3610967 < baseStart_3610967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610978 : List Nat := [3, 3, 2, 1, 1, 3, 2, 3, 1, 1, 3]
def baseStart_3610978 : Nat := 118140960795 + 3610978 * 2 ^ 59
def prefixEnd_3610978 : Nat := 4983230072969 + 3 ^ 40 * 3610978 * 2
def baseEnd_3610978 : Nat := 1854167346811078265668421

theorem tailTrace_3610978 : CollatzResearch.WordTrace tailWord_3610978 prefixEnd_3610978 1854167346811078265668421 := by
  unfold tailWord_3610978
  simp only [CollatzResearch.WordTrace]
  refine ⟨32925796878012721697260397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87802125008033924526027725 32925796878012721697260397)
  ·
    refine ⟨12347173829254770636472649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32925796878012721697260397 12347173829254770636472649)
    ·
      refine ⟨9260380371941077977354487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12347173829254770636472649 9260380371941077977354487)
      ·
        refine ⟨13890570557911616966031731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9260380371941077977354487 13890570557911616966031731)
        ·
          refine ⟨20835855836867425449047597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13890570557911616966031731 20835855836867425449047597)
          ·
            refine ⟨7813445938825284543392849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20835855836867425449047597 7813445938825284543392849)
            ·
              refine ⟨5860084454118963407544637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7813445938825284543392849 5860084454118963407544637)
              ·
                refine ⟨2197531670294611277829239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5860084454118963407544637 2197531670294611277829239)
                ·
                  refine ⟨3296297505441916916743859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2197531670294611277829239 3296297505441916916743859)
                  ·
                    refine ⟨4944446258162875375115789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3296297505441916916743859 4944446258162875375115789)
                    ·
                      refine ⟨1854167346811078265668421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4944446258162875375115789 1854167346811078265668421)
                      ·
                        rfl

theorem cell23_3610978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_3610978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3610978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3610978 prefixEnd_3610978 := by exact prefixLift 3610978
  have htrace : WordTrace (prefixWord ++ tailWord_3610978) baseStart_3610978 baseEnd_3610978 := by
    simpa [prefixWord, tailWord_3610978, baseEnd_3610978] using wordTrace_append hprefix tailTrace_3610978
  have hstable : (prefixWord ++ tailWord_3610978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610978).length < 2 ^ (prefixWord ++ tailWord_3610978).sum := by decide
  have hdescent : baseEnd_3610978 < baseStart_3610978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610984 : List Nat := [2, 1, 4, 2, 2, 2, 1, 3, 1, 1, 4]
def baseStart_3610984 : Nat := 118140960795 + 3610984 * 2 ^ 59
def prefixEnd_3610984 : Nat := 4983230072969 + 3 ^ 40 * 3610984 * 2
def baseEnd_3610984 : Nat := 1854170427695005242193393

theorem tailTrace_3610984 : CollatzResearch.WordTrace tailWord_3610984 prefixEnd_3610984 1854170427695005242193393 := by
  unfold tailWord_3610984
  simp only [CollatzResearch.WordTrace]
  refine ⟨65851703175014574906880003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87802270900019433209173337 65851703175014574906880003)
  ·
    refine ⟨98777554762521862360320005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65851703175014574906880003 98777554762521862360320005)
    ·
      refine ⟨18520791517972849192560001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98777554762521862360320005 18520791517972849192560001)
      ·
        refine ⟨13890593638479636894420001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18520791517972849192560001 13890593638479636894420001)
        ·
          refine ⟨10417945228859727670815001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13890593638479636894420001 10417945228859727670815001)
          ·
            refine ⟨7813458921644795753111251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10417945228859727670815001 7813458921644795753111251)
            ·
              refine ⟨11720188382467193629666877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7813458921644795753111251 11720188382467193629666877)
              ·
                refine ⟨4395070643425197611125079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11720188382467193629666877 4395070643425197611125079)
                ·
                  refine ⟨6592605965137796416687619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4395070643425197611125079 6592605965137796416687619)
                  ·
                    refine ⟨9888908947706694625031429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6592605965137796416687619 9888908947706694625031429)
                    ·
                      refine ⟨1854170427695005242193393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9888908947706694625031429 1854170427695005242193393)
                      ·
                        rfl

theorem cell23_3610984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_3610984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3610984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3610984 prefixEnd_3610984 := by exact prefixLift 3610984
  have htrace : WordTrace (prefixWord ++ tailWord_3610984) baseStart_3610984 baseEnd_3610984 := by
    simpa [prefixWord, tailWord_3610984, baseEnd_3610984] using wordTrace_append hprefix tailTrace_3610984
  have hstable : (prefixWord ++ tailWord_3610984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610984).length < 2 ^ (prefixWord ++ tailWord_3610984).sum := by decide
  have hdescent : baseEnd_3610984 < baseStart_3610984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610987 : List Nat := [1, 1, 1, 1, 2, 2, 2, 7, 1, 2, 3]
def baseStart_3610987 : Nat := 118140960795 + 3610987 * 2 ^ 59
def prefixEnd_3610987 : Nat := 4983230072969 + 3 ^ 40 * 3610987 * 2
def baseEnd_3610987 : Nat := 1854171968136968730455879

theorem tailTrace_3610987 : CollatzResearch.WordTrace tailWord_3610987 prefixEnd_3610987 1854171968136968730455879 := by
  unfold tailWord_3610987
  simp only [CollatzResearch.WordTrace]
  refine ⟨131703515769018281326119215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87802343846012187550746143 131703515769018281326119215)
  ·
    refine ⟨197555273653527421989178823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131703515769018281326119215 197555273653527421989178823)
    ·
      refine ⟨296332910480291132983768235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197555273653527421989178823 296332910480291132983768235)
      ·
        refine ⟨444499365720436699475652353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296332910480291132983768235 444499365720436699475652353)
        ·
          refine ⟨333374524290327524606739265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 444499365720436699475652353 333374524290327524606739265)
          ·
            refine ⟨250030893217745643455054449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 333374524290327524606739265 250030893217745643455054449)
            ·
              refine ⟨187523169913309232591290837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250030893217745643455054449 187523169913309232591290837)
              ·
                refine ⟨4395074294843185138858379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 187523169913309232591290837 4395074294843185138858379)
                ·
                  refine ⟨6592611442264777708287569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4395074294843185138858379 6592611442264777708287569)
                  ·
                    refine ⟨4944458581698583281215677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6592611442264777708287569 4944458581698583281215677)
                    ·
                      refine ⟨1854171968136968730455879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4944458581698583281215677 1854171968136968730455879)
                      ·
                        rfl

theorem cell23_3610987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 7, 1, 2, 3].length) (baseStart_3610987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3610987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3610987 prefixEnd_3610987 := by exact prefixLift 3610987
  have htrace : WordTrace (prefixWord ++ tailWord_3610987) baseStart_3610987 baseEnd_3610987 := by
    simpa [prefixWord, tailWord_3610987, baseEnd_3610987] using wordTrace_append hprefix tailTrace_3610987
  have hstable : (prefixWord ++ tailWord_3610987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610987).length < 2 ^ (prefixWord ++ tailWord_3610987).sum := by decide
  have hdescent : baseEnd_3610987 < baseStart_3610987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3610994 : List Nat := [3, 2, 1, 2, 1, 3, 3, 2, 2, 4]
def baseStart_3610994 : Nat := 118140960795 + 3610994 * 2 ^ 59
def prefixEnd_3610994 : Nat := 4983230072969 + 3 ^ 40 * 3610994 * 2
def baseEnd_3610994 : Nat := 618058520833850067689449

theorem tailTrace_3610994 : CollatzResearch.WordTrace tailWord_3610994 prefixEnd_3610994 618058520833850067689449 := by
  unfold tailWord_3610994
  simp only [CollatzResearch.WordTrace]
  refine ⟨32925942769998230380406009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87802514053328614347749357 32925942769998230380406009)
  ·
    refine ⟨24694457077498672785304507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32925942769998230380406009 24694457077498672785304507)
    ·
      refine ⟨37041685616248009177956761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24694457077498672785304507 37041685616248009177956761)
      ·
        refine ⟨27781264212186006883467571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37041685616248009177956761 27781264212186006883467571)
        ·
          refine ⟨41671896318279010325201357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27781264212186006883467571 41671896318279010325201357)
          ·
            refine ⟨15626961119354628871950509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41671896318279010325201357 15626961119354628871950509)
            ·
              refine ⟨5860110419757985826981441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15626961119354628871950509 5860110419757985826981441)
              ·
                refine ⟨4395082814818489370236081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5860110419757985826981441 4395082814818489370236081)
                ·
                  refine ⟨3296312111113867027677061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4395082814818489370236081 3296312111113867027677061)
                  ·
                    refine ⟨618058520833850067689449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3296312111113867027677061 618058520833850067689449)
                    ·
                      rfl

theorem cell23_3610994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 2, 2, 4].length) (baseStart_3610994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3610994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3610994 prefixEnd_3610994 := by exact prefixLift 3610994
  have htrace : WordTrace (prefixWord ++ tailWord_3610994) baseStart_3610994 baseEnd_3610994 := by
    simpa [prefixWord, tailWord_3610994, baseEnd_3610994] using wordTrace_append hprefix tailTrace_3610994
  have hstable : (prefixWord ++ tailWord_3610994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3610994).length < 2 ^ (prefixWord ++ tailWord_3610994).sum := by decide
  have hdescent : baseEnd_3610994 < baseStart_3610994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3610994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611000 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 1, 9, 3]
def baseStart_3611000 : Nat := 118140960795 + 3611000 * 2 ^ 59
def prefixEnd_3611000 : Nat := 4983230072969 + 3 ^ 40 * 3611000 * 2
def baseEnd_3611000 : Nat := 1854178643385477179593319

theorem tailTrace_3611000 : CollatzResearch.WordTrace tailWord_3611000 prefixEnd_3611000 1854178643385477179593319 := by
  unfold tailWord_3611000
  simp only [CollatzResearch.WordTrace]
  refine ⟨65851994958985592273171227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87802659945314123030894969 65851994958985592273171227)
  ·
    refine ⟨98777992438478388409756841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65851994958985592273171227 98777992438478388409756841)
    ·
      refine ⟨74083494328858791307317631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98777992438478388409756841 74083494328858791307317631)
      ·
        refine ⟨111125241493288186960976447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74083494328858791307317631 111125241493288186960976447)
        ·
          refine ⟨166687862239932280441464671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111125241493288186960976447 166687862239932280441464671)
          ·
            refine ⟨250031793359898420662197007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166687862239932280441464671 250031793359898420662197007)
            ·
              refine ⟨375047690039847630993295511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250031793359898420662197007 375047690039847630993295511)
              ·
                refine ⟨562571535059771446489943267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 375047690039847630993295511 562571535059771446489943267)
                ·
                  refine ⟨843857302589657169734914901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 562571535059771446489943267 843857302589657169734914901)
                  ·
                    refine ⟨4944476382361272478915517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 843857302589657169734914901 4944476382361272478915517)
                    ·
                      refine ⟨1854178643385477179593319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4944476382361272478915517 1854178643385477179593319)
                      ·
                        rfl

theorem cell23_3611000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 9, 3].length) (baseStart_3611000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3611000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3611000 prefixEnd_3611000 := by exact prefixLift 3611000
  have htrace : WordTrace (prefixWord ++ tailWord_3611000) baseStart_3611000 baseEnd_3611000 := by
    simpa [prefixWord, tailWord_3611000, baseEnd_3611000] using wordTrace_append hprefix tailTrace_3611000
  have hstable : (prefixWord ++ tailWord_3611000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611000).length < 2 ^ (prefixWord ++ tailWord_3611000).sum := by decide
  have hdescent : baseEnd_3611000 < baseStart_3611000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611011 : List Nat := [1, 1, 1, 3, 6, 1, 3, 1, 2, 4]
def baseStart_3611011 : Nat := 118140960795 + 3611011 * 2 ^ 59
def prefixEnd_3611011 : Nat := 4983230072969 + 3 ^ 40 * 3611011 * 2
def baseEnd_3611011 : Nat := 618061430557558878851923

theorem tailTrace_3611011 : CollatzResearch.WordTrace tailWord_3611011 prefixEnd_3611011 618061430557558878851923 := by
  unfold tailWord_3611011
  simp only [CollatzResearch.WordTrace]
  refine ⟨131704391120931333424992887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87802927413954222283328591 131704391120931333424992887)
  ·
    refine ⟨197556586681397000137489331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131704391120931333424992887 197556586681397000137489331)
    ·
      refine ⟨296334880022095500206233997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197556586681397000137489331 296334880022095500206233997)
      ·
        refine ⟨111125580008285812577337749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 296334880022095500206233997 111125580008285812577337749)
        ·
          refine ⟨5209011562888397464562707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 111125580008285812577337749 5209011562888397464562707)
          ·
            refine ⟨7813517344332596196844061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5209011562888397464562707 7813517344332596196844061)
            ·
              refine ⟨2930069004124723573816523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7813517344332596196844061 2930069004124723573816523)
              ·
                refine ⟨4395103506187085360724785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2930069004124723573816523 4395103506187085360724785)
                ·
                  refine ⟨3296327629640314020543589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4395103506187085360724785 3296327629640314020543589)
                  ·
                    refine ⟨618061430557558878851923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3296327629640314020543589 618061430557558878851923)
                    ·
                      rfl

theorem cell23_3611011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3, 1, 2, 4].length) (baseStart_3611011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3611011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3611011 prefixEnd_3611011 := by exact prefixLift 3611011
  have htrace : WordTrace (prefixWord ++ tailWord_3611011) baseStart_3611011 baseEnd_3611011 := by
    simpa [prefixWord, tailWord_3611011, baseEnd_3611011] using wordTrace_append hprefix tailTrace_3611011
  have hstable : (prefixWord ++ tailWord_3611011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611011).length < 2 ^ (prefixWord ++ tailWord_3611011).sum := by decide
  have hdescent : baseEnd_3611011 < baseStart_3611011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611034 : List Nat := [3, 1, 1, 4, 1, 2, 1, 2, 4, 1, 3]
def baseStart_3611034 : Nat := 118140960795 + 3611034 * 2 ^ 59
def prefixEnd_3611034 : Nat := 4983230072969 + 3 ^ 40 * 3611034 * 2
def baseEnd_3611034 : Nat := 1854196101727730046568163

theorem tailTrace_3611034 : CollatzResearch.WordTrace tailWord_3611034 prefixEnd_3611034 1854196101727730046568163 := by
  unfold tailWord_3611034
  simp only [CollatzResearch.WordTrace]
  refine ⟨32926307499962002088270039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87803486666565338902053437 32926307499962002088270039)
  ·
    refine ⟨49389461249943003132405059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32926307499962002088270039 49389461249943003132405059)
    ·
      refine ⟨74084191874914504698607589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49389461249943003132405059 74084191874914504698607589)
      ·
        refine ⟨13890785976546469630988923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74084191874914504698607589 13890785976546469630988923)
        ·
          refine ⟨20836178964819704446483385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13890785976546469630988923 20836178964819704446483385)
          ·
            refine ⟨15627134223614778334862539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20836178964819704446483385 15627134223614778334862539)
            ·
              refine ⟨23440701335422167502293809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15627134223614778334862539 23440701335422167502293809)
              ·
                refine ⟨17580526001566625626720357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23440701335422167502293809 17580526001566625626720357)
                ·
                  refine ⟨3296348625293742305010067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17580526001566625626720357 3296348625293742305010067)
                  ·
                    refine ⟨4944522937940613457515101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3296348625293742305010067 4944522937940613457515101)
                    ·
                      refine ⟨1854196101727730046568163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4944522937940613457515101 1854196101727730046568163)
                      ·
                        rfl

theorem cell23_3611034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_3611034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3611034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3611034 prefixEnd_3611034 := by exact prefixLift 3611034
  have htrace : WordTrace (prefixWord ++ tailWord_3611034) baseStart_3611034 baseEnd_3611034 := by
    simpa [prefixWord, tailWord_3611034, baseEnd_3611034] using wordTrace_append hprefix tailTrace_3611034
  have hstable : (prefixWord ++ tailWord_3611034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611034).length < 2 ^ (prefixWord ++ tailWord_3611034).sum := by decide
  have hdescent : baseEnd_3611034 < baseStart_3611034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611068 : List Nat := [2, 2, 2, 4, 1, 1, 4, 1, 2, 1, 3]
def baseStart_3611068 : Nat := 118140960795 + 3611068 * 2 ^ 59
def prefixEnd_3611068 : Nat := 4983230072969 + 3 ^ 40 * 3611068 * 2
def baseEnd_3611068 : Nat := 1854213560069982913543007

theorem tailTrace_3611068 : CollatzResearch.WordTrace tailWord_3611068 prefixEnd_3611068 1854213560069982913543007 := by
  unfold tailWord_3611068
  simp only [CollatzResearch.WordTrace]
  refine ⟨65853235040862416079908929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87804313387816554773211905 65853235040862416079908929)
  ·
    refine ⟨49389926280646812059931697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65853235040862416079908929 49389926280646812059931697)
    ·
      refine ⟨37042444710485109044948773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49389926280646812059931697 37042444710485109044948773)
      ·
        refine ⟨6945458383215957945927895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37042444710485109044948773 6945458383215957945927895)
        ·
          refine ⟨10418187574823936918891843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6945458383215957945927895 10418187574823936918891843)
          ·
            refine ⟨15627281362235905378337765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10418187574823936918891843 15627281362235905378337765)
            ·
              refine ⟨2930115255419232258438331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15627281362235905378337765 2930115255419232258438331)
              ·
                refine ⟨4395172883128848387657497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2930115255419232258438331 4395172883128848387657497)
                ·
                  refine ⟨3296379662346636290743123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4395172883128848387657497 3296379662346636290743123)
                  ·
                    refine ⟨4944569493519954436114685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3296379662346636290743123 4944569493519954436114685)
                    ·
                      refine ⟨1854213560069982913543007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4944569493519954436114685 1854213560069982913543007)
                      ·
                        rfl

theorem cell23_3611068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_3611068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3611068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3611068 prefixEnd_3611068 := by exact prefixLift 3611068
  have htrace : WordTrace (prefixWord ++ tailWord_3611068) baseStart_3611068 baseEnd_3611068 := by
    simpa [prefixWord, tailWord_3611068, baseEnd_3611068] using wordTrace_append hprefix tailTrace_3611068
  have hstable : (prefixWord ++ tailWord_3611068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611068).length < 2 ^ (prefixWord ++ tailWord_3611068).sum := by decide
  have hdescent : baseEnd_3611068 < baseStart_3611068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611094 : List Nat := [5, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5]
def baseStart_3611094 : Nat := 118140960795 + 3611094 * 2 ^ 59
def prefixEnd_3611094 : Nat := 4983230072969 + 3 ^ 40 * 3611094 * 2
def baseEnd_3611094 : Nat := 1854226910566999811817887

theorem tailTrace_3611094 : CollatzResearch.WordTrace tailWord_3611094 prefixEnd_3611094 1854226910566999811817887 := by
  unfold tailWord_3611094
  simp only [CollatzResearch.WordTrace]
  refine ⟨8231713648726914912516521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87804945586420425733509557 8231713648726914912516521)
  ·
    refine ⟨6173785236545186184387391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8231713648726914912516521 6173785236545186184387391)
    ·
      refine ⟨9260677854817779276581087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6173785236545186184387391 9260677854817779276581087)
      ·
        refine ⟨13891016782226668914871631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9260677854817779276581087 13891016782226668914871631)
        ·
          refine ⟨20836525173340003372307447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13891016782226668914871631 20836525173340003372307447)
          ·
            refine ⟨31254787760010005058461171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20836525173340003372307447 31254787760010005058461171)
            ·
              refine ⟨46882181640015007587691757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31254787760010005058461171 46882181640015007587691757)
              ·
                refine ⟨17580818115005627845384409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46882181640015007587691757 17580818115005627845384409)
                ·
                  refine ⟨13185613586254220884038307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17580818115005627845384409 13185613586254220884038307)
                  ·
                    refine ⟨19778420379381331326057461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13185613586254220884038307 19778420379381331326057461)
                    ·
                      refine ⟨1854226910566999811817887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19778420379381331326057461 1854226910566999811817887)
                      ·
                        rfl

theorem cell23_3611094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_3611094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3611094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3611094 prefixEnd_3611094 := by exact prefixLift 3611094
  have htrace : WordTrace (prefixWord ++ tailWord_3611094) baseStart_3611094 baseEnd_3611094 := by
    simpa [prefixWord, tailWord_3611094, baseEnd_3611094] using wordTrace_append hprefix tailTrace_3611094
  have hstable : (prefixWord ++ tailWord_3611094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611094).length < 2 ^ (prefixWord ++ tailWord_3611094).sum := by decide
  have hdescent : baseEnd_3611094 < baseStart_3611094 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611264 : List Nat := [2, 1, 1, 2, 1, 6, 1, 2, 1, 6]
def baseStart_3611264 : Nat := 118140960795 + 3611264 * 2 ^ 59
def prefixEnd_3611264 : Nat := 4983230072969 + 3 ^ 40 * 3611264 * 2
def baseEnd_3611264 : Nat := 618104734092754715564035

theorem tailTrace_3611264 : CollatzResearch.WordTrace tailWord_3611264 prefixEnd_3611264 618104734092754715564035 := by
  unfold tailWord_3611264
  simp only [CollatzResearch.WordTrace]
  refine ⟨65856809394507378816976423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87809079192676505089301897 65856809394507378816976423)
  ·
    refine ⟨98785214091761068225464635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65856809394507378816976423 98785214091761068225464635)
    ·
      refine ⟨148177821137641602338196953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98785214091761068225464635 148177821137641602338196953)
      ·
        refine ⟨111133365853231201753647715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148177821137641602338196953 111133365853231201753647715)
        ·
          refine ⟨166700048779846802630471573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111133365853231201753647715 166700048779846802630471573)
          ·
            refine ⟨7814064786555318873303355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 166700048779846802630471573 7814064786555318873303355)
            ·
              refine ⟨11721097179832978309955033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7814064786555318873303355 11721097179832978309955033)
              ·
                refine ⟨8790822884874733732466275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11721097179832978309955033 8790822884874733732466275)
                ·
                  refine ⟨13186234327312100598699413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8790822884874733732466275 13186234327312100598699413)
                  ·
                    refine ⟨618104734092754715564035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13186234327312100598699413 618104734092754715564035)
                    ·
                      rfl

theorem cell23_3611264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 2, 1, 6].length) (baseStart_3611264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3611264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3611264 prefixEnd_3611264 := by exact prefixLift 3611264
  have htrace : WordTrace (prefixWord ++ tailWord_3611264) baseStart_3611264 baseEnd_3611264 := by
    simpa [prefixWord, tailWord_3611264, baseEnd_3611264] using wordTrace_append hprefix tailTrace_3611264
  have hstable : (prefixWord ++ tailWord_3611264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611264).length < 2 ^ (prefixWord ++ tailWord_3611264).sum := by decide
  have hdescent : baseEnd_3611264 < baseStart_3611264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611268 : List Nat := [2, 3, 2, 1, 3, 2, 3, 1, 1, 5]
def baseStart_3611268 : Nat := 118140960795 + 3611268 * 2 ^ 59
def prefixEnd_3611268 : Nat := 4983230072969 + 3 ^ 40 * 3611268 * 2
def baseEnd_3611268 : Nat := 618105418733627377014029

theorem tailTrace_3611268 : CollatzResearch.WordTrace tailWord_3611268 prefixEnd_3611268 618105418733627377014029 := by
  unfold tailWord_3611268
  simp only [CollatzResearch.WordTrace]
  refine ⟨65856882340500133158549229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87809176454000177544732305 65856882340500133158549229)
  ·
    refine ⟨24696330877687549934455961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65856882340500133158549229 24696330877687549934455961)
    ·
      refine ⟨18522248158265662450841971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24696330877687549934455961 18522248158265662450841971)
      ·
        refine ⟨27783372237398493676262957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18522248158265662450841971 27783372237398493676262957)
        ·
          refine ⟨10418764589024435128598609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27783372237398493676262957 10418764589024435128598609)
          ·
            refine ⟨7814073441768326346448957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10418764589024435128598609 7814073441768326346448957)
            ·
              refine ⟨2930277540663122379918359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7814073441768326346448957 2930277540663122379918359)
              ·
                refine ⟨4395416310994683569877539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2930277540663122379918359 4395416310994683569877539)
                ·
                  refine ⟨6593124466492025354816309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4395416310994683569877539 6593124466492025354816309)
                  ·
                    refine ⟨618105418733627377014029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6593124466492025354816309 618105418733627377014029)
                    ·
                      rfl

theorem cell23_3611268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3, 1, 1, 5].length) (baseStart_3611268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3611268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3611268 prefixEnd_3611268 := by exact prefixLift 3611268
  have htrace : WordTrace (prefixWord ++ tailWord_3611268) baseStart_3611268 baseEnd_3611268 := by
    simpa [prefixWord, tailWord_3611268, baseEnd_3611268] using wordTrace_append hprefix tailTrace_3611268
  have hstable : (prefixWord ++ tailWord_3611268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611268).length < 2 ^ (prefixWord ++ tailWord_3611268).sum := by decide
  have hdescent : baseEnd_3611268 < baseStart_3611268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611282 : List Nat := [3, 2, 3, 1, 2, 1, 4, 2, 1, 1, 3]
def baseStart_3611282 : Nat := 118140960795 + 3611282 * 2 ^ 59
def prefixEnd_3611282 : Nat := 4983230072969 + 3 ^ 40 * 3611282 * 2
def baseEnd_3611282 : Nat := 1854323444930045076267023

theorem tailTrace_3611282 : CollatzResearch.WordTrace tailWord_3611282 prefixEnd_3611282 1854323444930045076267023 := by
  unfold tailWord_3611282
  simp only [CollatzResearch.WordTrace]
  refine ⟨32928568825737386677027025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87809516868633031138738733 32928568825737386677027025)
  ·
    refine ⟨24696426619303040007770269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32928568825737386677027025 24696426619303040007770269)
    ·
      refine ⟨9261159982238640002913851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24696426619303040007770269 9261159982238640002913851)
      ·
        refine ⟨13891739973357960004370777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9261159982238640002913851 13891739973357960004370777)
        ·
          refine ⟨10418804980018470003278083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13891739973357960004370777 10418804980018470003278083)
          ·
            refine ⟨15628207470027705004917125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10418804980018470003278083 15628207470027705004917125)
            ·
              refine ⟨2930288900630194688421961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15628207470027705004917125 2930288900630194688421961)
              ·
                refine ⟨2197716675472646016316471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2930288900630194688421961 2197716675472646016316471)
                ·
                  refine ⟨3296575013208969024474707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2197716675472646016316471 3296575013208969024474707)
                  ·
                    refine ⟨4944862519813453536712061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3296575013208969024474707 4944862519813453536712061)
                    ·
                      refine ⟨1854323444930045076267023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4944862519813453536712061 1854323444930045076267023)
                      ·
                        rfl

theorem cell23_3611282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_3611282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3611282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3611282 prefixEnd_3611282 := by exact prefixLift 3611282
  have htrace : WordTrace (prefixWord ++ tailWord_3611282) baseStart_3611282 baseEnd_3611282 := by
    simpa [prefixWord, tailWord_3611282, baseEnd_3611282] using wordTrace_append hprefix tailTrace_3611282
  have hstable : (prefixWord ++ tailWord_3611282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611282).length < 2 ^ (prefixWord ++ tailWord_3611282).sum := by decide
  have hdescent : baseEnd_3611282 < baseStart_3611282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611288 : List Nat := [2, 1, 2, 4, 1, 1, 2, 3, 3, 2, 2]
def baseStart_3611288 : Nat := 118140960795 + 3611288 * 2 ^ 59
def prefixEnd_3611288 : Nat := 4983230072969 + 3 ^ 40 * 3611288 * 2
def baseEnd_3611288 : Nat := 1854326525813972052791995

theorem tailTrace_3611288 : CollatzResearch.WordTrace tailWord_3611288 prefixEnd_3611288 1854326525813972052791995 := by
  unfold tailWord_3611288
  simp only [CollatzResearch.WordTrace]
  refine ⟨65857247070463904866413259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87809662760618539821884345 65857247070463904866413259)
  ·
    refine ⟨98785870605695857299619889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65857247070463904866413259 98785870605695857299619889)
    ·
      refine ⟨74089402954271892974714917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98785870605695857299619889 74089402954271892974714917)
      ·
        refine ⟨13891763053925979932759047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74089402954271892974714917 13891763053925979932759047)
        ·
          refine ⟨20837644580888969899138571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13891763053925979932759047 20837644580888969899138571)
          ·
            refine ⟨31256466871333454848707857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20837644580888969899138571 31256466871333454848707857)
            ·
              refine ⟨23442350153500091136530893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31256466871333454848707857 23442350153500091136530893)
              ·
                refine ⟨8790881307562534176199085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23442350153500091136530893 8790881307562534176199085)
                ·
                  refine ⟨3296580490335950316074657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8790881307562534176199085 3296580490335950316074657)
                  ·
                    refine ⟨2472435367751962737055993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3296580490335950316074657 2472435367751962737055993)
                    ·
                      refine ⟨1854326525813972052791995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2472435367751962737055993 1854326525813972052791995)
                      ·
                        rfl

theorem cell23_3611288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_3611288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3611288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3611288 prefixEnd_3611288 := by exact prefixLift 3611288
  have htrace : WordTrace (prefixWord ++ tailWord_3611288) baseStart_3611288 baseEnd_3611288 := by
    simpa [prefixWord, tailWord_3611288, baseEnd_3611288] using wordTrace_append hprefix tailTrace_3611288
  have hstable : (prefixWord ++ tailWord_3611288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611288).length < 2 ^ (prefixWord ++ tailWord_3611288).sum := by decide
  have hdescent : baseEnd_3611288 < baseStart_3611288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611321 : List Nat := [1, 2, 1, 4, 1, 1, 1, 4, 4, 1, 3]
def baseStart_3611321 : Nat := 118140960795 + 3611321 * 2 ^ 59
def prefixEnd_3611321 : Nat := 4983230072969 + 3 ^ 40 * 3611321 * 2
def baseEnd_3611321 : Nat := 1854343470675570423679343

theorem tailTrace_3611321 : CollatzResearch.WordTrace tailWord_3611321 prefixEnd_3611321 1854343470675570423679343 := by
  unfold tailWord_3611321
  simp only [CollatzResearch.WordTrace]
  refine ⟨131715697749808256368777817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87810465166538837579185211 131715697749808256368777817)
  ·
    refine ⟨98786773312356192276583363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131715697749808256368777817 98786773312356192276583363)
    ·
      refine ⟨148180159968534288414875045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98786773312356192276583363 148180159968534288414875045)
      ·
        refine ⟨27783779994100179077789071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148180159968534288414875045 27783779994100179077789071)
        ·
          refine ⟨41675669991150268616683607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27783779994100179077789071 41675669991150268616683607)
          ·
            refine ⟨62513504986725402925025411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41675669991150268616683607 62513504986725402925025411)
            ·
              refine ⟨93770257480088104387538117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62513504986725402925025411 93770257480088104387538117)
              ·
                refine ⟨17581923277516519572663397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93770257480088104387538117 17581923277516519572663397)
                ·
                  refine ⟨3296610614534347419874387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17581923277516519572663397 3296610614534347419874387)
                  ·
                    refine ⟨4944915921801521129811581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3296610614534347419874387 4944915921801521129811581)
                    ·
                      refine ⟨1854343470675570423679343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4944915921801521129811581 1854343470675570423679343)
                      ·
                        rfl

theorem cell23_3611321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 4, 1, 3].length) (baseStart_3611321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3611321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3611321 prefixEnd_3611321 := by exact prefixLift 3611321
  have htrace : WordTrace (prefixWord ++ tailWord_3611321) baseStart_3611321 baseEnd_3611321 := by
    simpa [prefixWord, tailWord_3611321, baseEnd_3611321] using wordTrace_append hprefix tailTrace_3611321
  have hstable : (prefixWord ++ tailWord_3611321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611321).length < 2 ^ (prefixWord ++ tailWord_3611321).sum := by decide
  have hdescent : baseEnd_3611321 < baseStart_3611321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611325 : List Nat := [1, 4, 1, 2, 1, 5, 2, 1, 1, 2, 3]
def baseStart_3611325 : Nat := 118140960795 + 3611325 * 2 ^ 59
def prefixEnd_3611325 : Nat := 4983230072969 + 3 ^ 40 * 3611325 * 2
def baseEnd_3611325 : Nat := 1854345524598188408029325

theorem tailTrace_3611325 : CollatzResearch.WordTrace tailWord_3611325 prefixEnd_3611325 1854345524598188408029325 := by
  unfold tailWord_3611325
  simp only [CollatzResearch.WordTrace]
  refine ⟨131715843641793765051923429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87810562427862510034615619 131715843641793765051923429)
  ·
    refine ⟨24696720682836330947235643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131715843641793765051923429 24696720682836330947235643)
    ·
      refine ⟨37045081024254496420853465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24696720682836330947235643 37045081024254496420853465)
      ·
        refine ⟨27783810768190872315640099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37045081024254496420853465 27783810768190872315640099)
        ·
          refine ⟨41675716152286308473460149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27783810768190872315640099 41675716152286308473460149)
          ·
            refine ⟨3907098389276841419386889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41675716152286308473460149 3907098389276841419386889)
            ·
              refine ⟨2930323791957631064540167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3907098389276841419386889 2930323791957631064540167)
              ·
                refine ⟨4395485687936446596810251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2930323791957631064540167 4395485687936446596810251)
                ·
                  refine ⟨6593228531904669895215377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4395485687936446596810251 6593228531904669895215377)
                  ·
                    refine ⟨4944921398928502421411533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6593228531904669895215377 4944921398928502421411533)
                    ·
                      refine ⟨1854345524598188408029325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4944921398928502421411533 1854345524598188408029325)
                      ·
                        rfl

theorem cell23_3611325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2, 1, 1, 2, 3].length) (baseStart_3611325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3611325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3611325 prefixEnd_3611325 := by exact prefixLift 3611325
  have htrace : WordTrace (prefixWord ++ tailWord_3611325) baseStart_3611325 baseEnd_3611325 := by
    simpa [prefixWord, tailWord_3611325, baseEnd_3611325] using wordTrace_append hprefix tailTrace_3611325
  have hstable : (prefixWord ++ tailWord_3611325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611325).length < 2 ^ (prefixWord ++ tailWord_3611325).sum := by decide
  have hdescent : baseEnd_3611325 < baseStart_3611325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611338 : List Nat := [3, 1, 2, 1, 4, 2, 1, 1, 4, 1, 3]
def baseStart_3611338 : Nat := 118140960795 + 3611338 * 2 ^ 59
def prefixEnd_3611338 : Nat := 4983230072969 + 3 ^ 40 * 3611338 * 2
def baseEnd_3611338 : Nat := 1854352199846696857166765

theorem tailTrace_3611338 : CollatzResearch.WordTrace tailWord_3611338 prefixEnd_3611338 1854352199846696857166765 := by
  unfold tailWord_3611338
  simp only [CollatzResearch.WordTrace]
  refine ⟨32929079447686667068036667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87810878527164445514764445 32929079447686667068036667)
  ·
    refine ⟨49393619171530000602055001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32929079447686667068036667 49393619171530000602055001)
    ·
      refine ⟨37045214378647500451541251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49393619171530000602055001 37045214378647500451541251)
      ·
        refine ⟨55567821567971250677311877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37045214378647500451541251 55567821567971250677311877)
        ·
          refine ⟨10418966543994609501995977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55567821567971250677311877 10418966543994609501995977)
          ·
            refine ⟨7814224907995957126496983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10418966543994609501995977 7814224907995957126496983)
            ·
              refine ⟨11721337361993935689745475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7814224907995957126496983 11721337361993935689745475)
              ·
                refine ⟨17582006042990903534618213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11721337361993935689745475 17582006042990903534618213)
                ·
                  refine ⟨3296626133060794412740915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17582006042990903534618213 3296626133060794412740915)
                  ·
                    refine ⟨4944939199591191619111373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3296626133060794412740915 4944939199591191619111373)
                    ·
                      refine ⟨1854352199846696857166765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4944939199591191619111373 1854352199846696857166765)
                      ·
                        rfl

theorem cell23_3611338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 4, 1, 3].length) (baseStart_3611338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3611338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3611338 prefixEnd_3611338 := by exact prefixLift 3611338
  have htrace : WordTrace (prefixWord ++ tailWord_3611338) baseStart_3611338 baseEnd_3611338 := by
    simpa [prefixWord, tailWord_3611338, baseEnd_3611338] using wordTrace_append hprefix tailTrace_3611338
  have hstable : (prefixWord ++ tailWord_3611338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611338).length < 2 ^ (prefixWord ++ tailWord_3611338).sum := by decide
  have hdescent : baseEnd_3611338 < baseStart_3611338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611354 : List Nat := [3, 1, 1, 2, 2, 2, 1, 3, 2, 6]
def baseStart_3611354 : Nat := 118140960795 + 3611354 * 2 ^ 59
def prefixEnd_3611354 : Nat := 4983230072969 + 3 ^ 40 * 3611354 * 2
def baseEnd_3611354 : Nat := 618120138512389598188897

theorem tailTrace_3611354 : CollatzResearch.WordTrace tailWord_3611354 prefixEnd_3611354 618120138512389598188897 := by
  unfold tailWord_3611354
  simp only [CollatzResearch.WordTrace]
  refine ⟨32929225339672175751182279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87811267572459135336486077 32929225339672175751182279)
  ·
    refine ⟨49393838009508263626773419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32929225339672175751182279 49393838009508263626773419)
    ·
      refine ⟨74090757014262395440160129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49393838009508263626773419 74090757014262395440160129)
      ·
        refine ⟨55568067760696796580120097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74090757014262395440160129 55568067760696796580120097)
        ·
          refine ⟨41676050820522597435090073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55568067760696796580120097 41676050820522597435090073)
          ·
            refine ⟨31257038115391948076317555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41676050820522597435090073 31257038115391948076317555)
            ·
              refine ⟨46885557173087922114476333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31257038115391948076317555 46885557173087922114476333)
              ·
                refine ⟨17582083939907970792928625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46885557173087922114476333 17582083939907970792928625)
                ·
                  refine ⟨13186562954930978094696469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17582083939907970792928625 13186562954930978094696469)
                  ·
                    refine ⟨618120138512389598188897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13186562954930978094696469 618120138512389598188897)
                    ·
                      rfl

theorem cell23_3611354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 2, 6].length) (baseStart_3611354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3611354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3611354 prefixEnd_3611354 := by exact prefixLift 3611354
  have htrace : WordTrace (prefixWord ++ tailWord_3611354) baseStart_3611354 baseEnd_3611354 := by
    simpa [prefixWord, tailWord_3611354, baseEnd_3611354] using wordTrace_append hprefix tailTrace_3611354
  have hstable : (prefixWord ++ tailWord_3611354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611354).length < 2 ^ (prefixWord ++ tailWord_3611354).sum := by decide
  have hdescent : baseEnd_3611354 < baseStart_3611354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611365 : List Nat := [1, 3, 1, 4, 1, 3, 2, 2, 1, 3, 2]
def baseStart_3611365 : Nat := 118140960795 + 3611365 * 2 ^ 59
def prefixEnd_3611365 : Nat := 4983230072969 + 3 ^ 40 * 3611365 * 2
def baseEnd_3611365 : Nat := 1854366063824368251529141

theorem tailTrace_3611365 : CollatzResearch.WordTrace tailWord_3611365 prefixEnd_3611365 1854366063824368251529141 := by
  unfold tailWord_3611365
  simp only [CollatzResearch.WordTrace]
  refine ⟨131717302561648851883379549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87811535041099234588919699 131717302561648851883379549)
  ·
    refine ⟨49393988460618319456267331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131717302561648851883379549 49393988460618319456267331)
    ·
      refine ⟨74090982690927479184400997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49393988460618319456267331 74090982690927479184400997)
      ·
        refine ⟨13892059254548902347075187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74090982690927479184400997 13892059254548902347075187)
        ·
          refine ⟨20838088881823353520612781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13892059254548902347075187 20838088881823353520612781)
          ·
            refine ⟨7814283330683757570229793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20838088881823353520612781 7814283330683757570229793)
            ·
              refine ⟨5860712498012818177672345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7814283330683757570229793 5860712498012818177672345)
              ·
                refine ⟨4395534373509613633254259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5860712498012818177672345 4395534373509613633254259)
                ·
                  refine ⟨6593301560264420449881389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4395534373509613633254259 6593301560264420449881389)
                  ·
                    refine ⟨2472488085099157668705521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6593301560264420449881389 2472488085099157668705521)
                    ·
                      refine ⟨1854366063824368251529141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2472488085099157668705521 1854366063824368251529141)
                      ·
                        rfl

theorem cell23_3611365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_3611365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3611365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3611365 prefixEnd_3611365 := by exact prefixLift 3611365
  have htrace : WordTrace (prefixWord ++ tailWord_3611365) baseStart_3611365 baseEnd_3611365 := by
    simpa [prefixWord, tailWord_3611365, baseEnd_3611365] using wordTrace_append hprefix tailTrace_3611365
  have hstable : (prefixWord ++ tailWord_3611365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611365).length < 2 ^ (prefixWord ++ tailWord_3611365).sum := by decide
  have hdescent : baseEnd_3611365 < baseStart_3611365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611401 : List Nat := [1, 2, 1, 1, 3, 2, 2, 6, 5]
def baseStart_3611401 : Nat := 118140960795 + 3611401 * 2 ^ 59
def prefixEnd_3611401 : Nat := 4983230072969 + 3 ^ 40 * 3611401 * 2
def baseEnd_3611401 : Nat := 206042727680881123408775

theorem tailTrace_3611401 : CollatzResearch.WordTrace tailWord_3611401 prefixEnd_3611401 206042727680881123408775 := by
  unfold tailWord_3611401
  simp only [CollatzResearch.WordTrace]
  refine ⟨131718615589518430031690057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87812410393012286687793371 131718615589518430031690057)
  ·
    refine ⟨98788961692138822523767543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131718615589518430031690057 98788961692138822523767543)
    ·
      refine ⟨148183442538208233785651315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98788961692138822523767543 148183442538208233785651315)
      ·
        refine ⟨222275163807312350678476973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148183442538208233785651315 222275163807312350678476973)
        ·
          refine ⟨83353186427742131504428865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222275163807312350678476973 83353186427742131504428865)
          ·
            refine ⟨62514889820806598628321649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83353186427742131504428865 62514889820806598628321649)
            ·
              refine ⟨46886167365604948971241237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62514889820806598628321649 46886167365604948971241237)
              ·
                refine ⟨2197789095262731983026933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46886167365604948971241237 2197789095262731983026933)
                ·
                  refine ⟨206042727680881123408775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2197789095262731983026933 206042727680881123408775)
                  ·
                    rfl

theorem cell23_3611401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 6, 5].length) (baseStart_3611401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3611401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3611401 prefixEnd_3611401 := by exact prefixLift 3611401
  have htrace : WordTrace (prefixWord ++ tailWord_3611401) baseStart_3611401 baseEnd_3611401 := by
    simpa [prefixWord, tailWord_3611401, baseEnd_3611401] using wordTrace_append hprefix tailTrace_3611401
  have hstable : (prefixWord ++ tailWord_3611401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611401).length < 2 ^ (prefixWord ++ tailWord_3611401).sum := by decide
  have hdescent : baseEnd_3611401 < baseStart_3611401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611462 : List Nat := [6, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3]
def baseStart_3611462 : Nat := 118140960795 + 3611462 * 2 ^ 59
def prefixEnd_3611462 : Nat := 4983230072969 + 3 ^ 40 * 3611462 * 2
def baseEnd_3611462 : Nat := 1854415871447854372016195

theorem tailTrace_3611462 : CollatzResearch.WordTrace tailWord_3611462 prefixEnd_3611462 1854415871447854372016195 := by
  unfold tailWord_3611462
  simp only [CollatzResearch.WordTrace]
  refine ⟨4116276263821794920301895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 87813893628198291633107093 4116276263821794920301895)
  ·
    refine ⟨6174414395732692380452843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4116276263821794920301895 6174414395732692380452843)
    ·
      refine ⟨9261621593599038570679265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6174414395732692380452843 9261621593599038570679265)
      ·
        refine ⟨6946216195199278928009449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9261621593599038570679265 6946216195199278928009449)
        ·
          refine ⟨5209662146399459196007087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6946216195199278928009449 5209662146399459196007087)
          ·
            refine ⟨7814493219599188794010631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5209662146399459196007087 7814493219599188794010631)
            ·
              refine ⟨11721739829398783191015947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7814493219599188794010631 11721739829398783191015947)
              ·
                refine ⟨17582609744098174786523921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11721739829398783191015947 17582609744098174786523921)
                ·
                  refine ⟨13186957308073631089892941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17582609744098174786523921 13186957308073631089892941)
                  ·
                    refine ⟨4945108990527611658709853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13186957308073631089892941 4945108990527611658709853)
                    ·
                      refine ⟨1854415871447854372016195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4945108990527611658709853 1854415871447854372016195)
                      ·
                        rfl

theorem cell23_3611462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_3611462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3611462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3611462 prefixEnd_3611462 := by exact prefixLift 3611462
  have htrace : WordTrace (prefixWord ++ tailWord_3611462) baseStart_3611462 baseEnd_3611462 := by
    simpa [prefixWord, tailWord_3611462, baseEnd_3611462] using wordTrace_append hprefix tailTrace_3611462
  have hstable : (prefixWord ++ tailWord_3611462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611462).length < 2 ^ (prefixWord ++ tailWord_3611462).sum := by decide
  have hdescent : baseEnd_3611462 < baseStart_3611462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611468 : List Nat := [2, 2, 1, 3, 3, 1, 1, 1, 1, 6, 2]
def baseStart_3611468 : Nat := 118140960795 + 3611468 * 2 ^ 59
def prefixEnd_3611468 : Nat := 4983230072969 + 3 ^ 40 * 3611468 * 2
def baseEnd_3611468 : Nat := 1854418952331781348541167

theorem tailTrace_3611468 : CollatzResearch.WordTrace tailWord_3611468 prefixEnd_3611468 1854418952331781348541167 := by
  unfold tailWord_3611468
  simp only [CollatzResearch.WordTrace]
  refine ⟨65860529640137850237189529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87814039520183800316252705 65860529640137850237189529)
  ·
    refine ⟨49395397230103387677892147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65860529640137850237189529 49395397230103387677892147)
    ·
      refine ⟨74093095845155081516838221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49395397230103387677892147 74093095845155081516838221)
      ·
        refine ⟨27784910941933155568814333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74093095845155081516838221 27784910941933155568814333)
        ·
          refine ⟨10419341603224933338305375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27784910941933155568814333 10419341603224933338305375)
          ·
            refine ⟨15629012404837400007458063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10419341603224933338305375 15629012404837400007458063)
            ·
              refine ⟨23443518607256100011187095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15629012404837400007458063 23443518607256100011187095)
              ·
                refine ⟨35165277910884150016780643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23443518607256100011187095 35165277910884150016780643)
                ·
                  refine ⟨52747916866326225025170965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35165277910884150016780643 52747916866326225025170965)
                  ·
                    refine ⟨2472558603109041798054889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 52747916866326225025170965 2472558603109041798054889)
                    ·
                      refine ⟨1854418952331781348541167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2472558603109041798054889 1854418952331781348541167)
                      ·
                        rfl

theorem cell23_3611468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 1, 6, 2].length) (baseStart_3611468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3611468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3611468 prefixEnd_3611468 := by exact prefixLift 3611468
  have htrace : WordTrace (prefixWord ++ tailWord_3611468) baseStart_3611468 baseEnd_3611468 := by
    simpa [prefixWord, tailWord_3611468, baseEnd_3611468] using wordTrace_append hprefix tailTrace_3611468
  have hstable : (prefixWord ++ tailWord_3611468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611468).length < 2 ^ (prefixWord ++ tailWord_3611468).sum := by decide
  have hdescent : baseEnd_3611468 < baseStart_3611468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611495 : List Nat := [1, 1, 5, 1, 2, 2, 1, 5, 1, 4]
def baseStart_3611495 : Nat := 118140960795 + 3611495 * 2 ^ 59
def prefixEnd_3611495 : Nat := 4983230072969 + 3 ^ 40 * 3611495 * 2
def baseEnd_3611495 : Nat := 618144272103150914301181

theorem tailTrace_3611495 : CollatzResearch.WordTrace tailWord_3611495 prefixEnd_3611495 618144272103150914301181 := by
  unfold tailWord_3611495
  simp only [CollatzResearch.WordTrace]
  refine ⟨131722044051177884085611939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87814696034118589390407959 131722044051177884085611939)
  ·
    refine ⟨197583066076766826128417909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131722044051177884085611939 197583066076766826128417909)
    ·
      refine ⟨18523412444696889949539179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 197583066076766826128417909 18523412444696889949539179)
      ·
        refine ⟨27785118667045334924308769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18523412444696889949539179 27785118667045334924308769)
        ·
          refine ⟨20838839000284001193231577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27785118667045334924308769 20838839000284001193231577)
          ·
            refine ⟨15629129250213000894923683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20838839000284001193231577 15629129250213000894923683)
            ·
              refine ⟨23443693875319501342385525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15629129250213000894923683 23443693875319501342385525)
              ·
                refine ⟨2197846300811203250848643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23443693875319501342385525 2197846300811203250848643)
                ·
                  refine ⟨3296769451216804876272965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2197846300811203250848643 3296769451216804876272965)
                  ·
                    refine ⟨618144272103150914301181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3296769451216804876272965 618144272103150914301181)
                    ·
                      rfl

theorem cell23_3611495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 5, 1, 4].length) (baseStart_3611495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3611495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3611495 prefixEnd_3611495 := by exact prefixLift 3611495
  have htrace : WordTrace (prefixWord ++ tailWord_3611495) baseStart_3611495 baseEnd_3611495 := by
    simpa [prefixWord, tailWord_3611495, baseEnd_3611495] using wordTrace_append hprefix tailTrace_3611495
  have hstable : (prefixWord ++ tailWord_3611495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611495).length < 2 ^ (prefixWord ++ tailWord_3611495).sum := by decide
  have hdescent : baseEnd_3611495 < baseStart_3611495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611552 : List Nat := [2, 1, 1, 4, 1, 1, 5, 3, 1, 1, 3]
def baseStart_3611552 : Nat := 118140960795 + 3611552 * 2 ^ 59
def prefixEnd_3611552 : Nat := 4983230072969 + 3 ^ 40 * 3611552 * 2
def baseEnd_3611552 : Nat := 1854462084706759019890781

theorem tailTrace_3611552 : CollatzResearch.WordTrace tailWord_3611552 prefixEnd_3611552 1854462084706759019890781 := by
  unfold tailWord_3611552
  simp only [CollatzResearch.WordTrace]
  refine ⟨65862061505985691410218455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87816082007980921880291273 65862061505985691410218455)
  ·
    refine ⟨98793092258978537115327683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65862061505985691410218455 98793092258978537115327683)
    ·
      refine ⟨148189638388467805672991525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98793092258978537115327683 148189638388467805672991525)
      ·
        refine ⟨27785557197837713563685911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148189638388467805672991525 27785557197837713563685911)
        ·
          refine ⟨41678335796756570345528867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27785557197837713563685911 41678335796756570345528867)
          ·
            refine ⟨62517503695134855518293301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41678335796756570345528867 62517503695134855518293301)
            ·
              refine ⟨5861015971418892704839997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62517503695134855518293301 5861015971418892704839997)
              ·
                refine ⟨2197880989282084764314999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5861015971418892704839997 2197880989282084764314999)
                ·
                  refine ⟨3296821483923127146472499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2197880989282084764314999 3296821483923127146472499)
                  ·
                    refine ⟨4945232225884690719708749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3296821483923127146472499 4945232225884690719708749)
                    ·
                      refine ⟨1854462084706759019890781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4945232225884690719708749 1854462084706759019890781)
                      ·
                        rfl

theorem cell23_3611552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 3, 1, 1, 3].length) (baseStart_3611552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3611552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3611552 prefixEnd_3611552 := by exact prefixLift 3611552
  have htrace : WordTrace (prefixWord ++ tailWord_3611552) baseStart_3611552 baseEnd_3611552 := by
    simpa [prefixWord, tailWord_3611552, baseEnd_3611552] using wordTrace_append hprefix tailTrace_3611552
  have hstable : (prefixWord ++ tailWord_3611552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611552).length < 2 ^ (prefixWord ++ tailWord_3611552).sum := by decide
  have hdescent : baseEnd_3611552 < baseStart_3611552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611569 : List Nat := [1, 2, 2, 4, 4, 1, 1, 1, 3, 1, 3]
def baseStart_3611569 : Nat := 118140960795 + 3611569 * 2 ^ 59
def prefixEnd_3611569 : Nat := 4983230072969 + 3 ^ 40 * 3611569 * 2
def baseEnd_3611569 : Nat := 1854470813877885453378203

theorem tailTrace_3611569 : CollatzResearch.WordTrace tailWord_3611569 prefixEnd_3611569 1854470813877885453378203 := by
  unfold tailWord_3611569
  simp only [CollatzResearch.WordTrace]
  refine ⟨131724743052909794723805761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87816495368606529815870507 131724743052909794723805761)
  ·
    refine ⟨98793557289682346042854321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131724743052909794723805761 98793557289682346042854321)
    ·
      refine ⟨74095167967261759532140741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98793557289682346042854321 74095167967261759532140741)
      ·
        refine ⟨13892843993861579912276389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74095167967261759532140741 13892843993861579912276389)
        ·
          refine ⟨2604908248849046233551823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13892843993861579912276389 2604908248849046233551823)
          ·
            refine ⟨3907362373273569350327735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2604908248849046233551823 3907362373273569350327735)
            ·
              refine ⟨5861043559910354025491603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3907362373273569350327735 5861043559910354025491603)
              ·
                refine ⟨8791565339865531038237405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5861043559910354025491603 8791565339865531038237405)
                ·
                  refine ⟨3296837002449574139339027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8791565339865531038237405 3296837002449574139339027)
                  ·
                    refine ⟨4945255503674361209008541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3296837002449574139339027 4945255503674361209008541)
                    ·
                      refine ⟨1854470813877885453378203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4945255503674361209008541 1854470813877885453378203)
                      ·
                        rfl

theorem cell23_3611569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_3611569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3611569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3611569 prefixEnd_3611569 := by exact prefixLift 3611569
  have htrace : WordTrace (prefixWord ++ tailWord_3611569) baseStart_3611569 baseEnd_3611569 := by
    simpa [prefixWord, tailWord_3611569, baseEnd_3611569] using wordTrace_append hprefix tailTrace_3611569
  have hstable : (prefixWord ++ tailWord_3611569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611569).length < 2 ^ (prefixWord ++ tailWord_3611569).sum := by decide
  have hdescent : baseEnd_3611569 < baseStart_3611569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611571 : List Nat := [1, 1, 1, 2, 3, 1, 2, 1, 5, 2, 4]
def baseStart_3611571 : Nat := 118140960795 + 3611571 * 2 ^ 59
def prefixEnd_3611571 : Nat := 4983230072969 + 3 ^ 40 * 3611571 * 2
def baseEnd_3611571 : Nat := 1854471840839194445553193

theorem tailTrace_3611571 : CollatzResearch.WordTrace tailWord_3611571 prefixEnd_3611571 1854471840839194445553193 := by
  unfold tailWord_3611571
  simp only [CollatzResearch.WordTrace]
  refine ⟨131724815998902549065378567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87816543999268366043585711 131724815998902549065378567)
  ·
    refine ⟨197587223998353823598067851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131724815998902549065378567 197587223998353823598067851)
    ·
      refine ⟨296380835997530735397101777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197587223998353823598067851 296380835997530735397101777)
      ·
        refine ⟨222285626998148051547826333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296380835997530735397101777 222285626998148051547826333)
        ·
          refine ⟨83357110124305519330434875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222285626998148051547826333 83357110124305519330434875)
          ·
            refine ⟨125035665186458278995652313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83357110124305519330434875 125035665186458278995652313)
            ·
              refine ⟨93776748889843709246739235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125035665186458278995652313 93776748889843709246739235)
              ·
                refine ⟨140665123334765563870108853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93776748889843709246739235 140665123334765563870108853)
                ·
                  refine ⟨13187355312634271612822705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 140665123334765563870108853 13187355312634271612822705)
                  ·
                    refine ⟨9890516484475703709617029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13187355312634271612822705 9890516484475703709617029)
                    ·
                      refine ⟨1854471840839194445553193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9890516484475703709617029 1854471840839194445553193)
                      ·
                        rfl

theorem cell23_3611571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5, 2, 4].length) (baseStart_3611571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3611571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3611571 prefixEnd_3611571 := by exact prefixLift 3611571
  have htrace : WordTrace (prefixWord ++ tailWord_3611571) baseStart_3611571 baseEnd_3611571 := by
    simpa [prefixWord, tailWord_3611571, baseEnd_3611571] using wordTrace_append hprefix tailTrace_3611571
  have hstable : (prefixWord ++ tailWord_3611571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611571).length < 2 ^ (prefixWord ++ tailWord_3611571).sum := by decide
  have hdescent : baseEnd_3611571 < baseStart_3611571 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611578 : List Nat := [3, 1, 1, 1, 2, 1, 4, 2, 3, 2, 3]
def baseStart_3611578 : Nat := 118140960795 + 3611578 * 2 ^ 59
def prefixEnd_3611578 : Nat := 4983230072969 + 3 ^ 40 * 3611578 * 2
def baseEnd_3611578 : Nat := 1854475435203775918165661

theorem tailTrace_3611578 : CollatzResearch.WordTrace tailWord_3611578 prefixEnd_3611578 1854475435203775918165661 := by
  unfold tailWord_3611578
  simp only [CollatzResearch.WordTrace]
  refine ⟨32931267827469297315220847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87816714206584792840588925 32931267827469297315220847)
  ·
    refine ⟨49396901741203945972831271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32931267827469297315220847 49396901741203945972831271)
    ·
      refine ⟨74095352611805918959246907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49396901741203945972831271 74095352611805918959246907)
      ·
        refine ⟨111143028917708878438870361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74095352611805918959246907 111143028917708878438870361)
        ·
          refine ⟨83357271688281658829152771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111143028917708878438870361 83357271688281658829152771)
          ·
            refine ⟨125035907532422488243729157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83357271688281658829152771 125035907532422488243729157)
            ·
              refine ⟨23444232662329216545699217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125035907532422488243729157 23444232662329216545699217)
              ·
                refine ⟨17583174496746912409274413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23444232662329216545699217 17583174496746912409274413)
                ·
                  refine ⟨6593690436280092153477905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17583174496746912409274413 6593690436280092153477905)
                  ·
                    refine ⟨4945267827210069115108429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6593690436280092153477905 4945267827210069115108429)
                    ·
                      refine ⟨1854475435203775918165661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4945267827210069115108429 1854475435203775918165661)
                      ·
                        rfl

theorem cell23_3611578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 3, 2, 3].length) (baseStart_3611578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3611578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3611578 prefixEnd_3611578 := by exact prefixLift 3611578
  have htrace : WordTrace (prefixWord ++ tailWord_3611578) baseStart_3611578 baseEnd_3611578 := by
    simpa [prefixWord, tailWord_3611578, baseEnd_3611578] using wordTrace_append hprefix tailTrace_3611578
  have hstable : (prefixWord ++ tailWord_3611578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611578).length < 2 ^ (prefixWord ++ tailWord_3611578).sum := by decide
  have hdescent : baseEnd_3611578 < baseStart_3611578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611592 : List Nat := [2, 1, 3, 1, 5, 2, 1, 2, 1, 1, 4]
def baseStart_3611592 : Nat := 118140960795 + 3611592 * 2 ^ 59
def prefixEnd_3611592 : Nat := 4983230072969 + 3 ^ 40 * 3611592 * 2
def baseEnd_3611592 : Nat := 1854482623932938863390597

theorem tailTrace_3611592 : CollatzResearch.WordTrace tailWord_3611592 prefixEnd_3611592 1854482623932938863390597 := by
  unfold tailWord_3611592
  simp only [CollatzResearch.WordTrace]
  refine ⟨65862790965913234825946515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87817054621217646434595353 65862790965913234825946515)
  ·
    refine ⟨98794186448869852238919773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65862790965913234825946515 98794186448869852238919773)
    ·
      refine ⟨37047819918326194589594915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98794186448869852238919773 37047819918326194589594915)
      ·
        refine ⟨55571729877489291884392373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37047819918326194589594915 55571729877489291884392373)
        ·
          refine ⟨5209849676014621114161785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55571729877489291884392373 5209849676014621114161785)
          ·
            refine ⟨3907387257010965835621339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5209849676014621114161785 3907387257010965835621339)
            ·
              refine ⟨5861080885516448753432009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3907387257010965835621339 5861080885516448753432009)
              ·
                refine ⟨4395810664137336565074007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5861080885516448753432009 4395810664137336565074007)
                ·
                  refine ⟨6593715996206004847611011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4395810664137336565074007 6593715996206004847611011)
                  ·
                    refine ⟨9890573994309007271416517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6593715996206004847611011 9890573994309007271416517)
                    ·
                      refine ⟨1854482623932938863390597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9890573994309007271416517 1854482623932938863390597)
                      ·
                        rfl

theorem cell23_3611592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 2, 1, 1, 4].length) (baseStart_3611592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3611592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3611592 prefixEnd_3611592 := by exact prefixLift 3611592
  have htrace : WordTrace (prefixWord ++ tailWord_3611592) baseStart_3611592 baseEnd_3611592 := by
    simpa [prefixWord, tailWord_3611592, baseEnd_3611592] using wordTrace_append hprefix tailTrace_3611592
  have hstable : (prefixWord ++ tailWord_3611592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611592).length < 2 ^ (prefixWord ++ tailWord_3611592).sum := by decide
  have hdescent : baseEnd_3611592 < baseStart_3611592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611595 : List Nat := [1, 1, 1, 1, 3, 5, 3, 2, 1, 2, 3]
def baseStart_3611595 : Nat := 118140960795 + 3611595 * 2 ^ 59
def prefixEnd_3611595 : Nat := 4983230072969 + 3 ^ 40 * 3611595 * 2
def baseEnd_3611595 : Nat := 1854484164374902351653083

theorem tailTrace_3611595 : CollatzResearch.WordTrace tailWord_3611595 prefixEnd_3611595 1854484164374902351653083 := by
  unfold tailWord_3611595
  simp only [CollatzResearch.WordTrace]
  refine ⟨131725691350815601164252239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87817127567210400776168159 131725691350815601164252239)
  ·
    refine ⟨197588537026223401746378359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131725691350815601164252239 197588537026223401746378359)
    ·
      refine ⟨296382805539335102619567539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197588537026223401746378359 296382805539335102619567539)
      ·
        refine ⟨444574208309002653929351309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296382805539335102619567539 444574208309002653929351309)
        ·
          refine ⟨166715328115875995223506741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 444574208309002653929351309 166715328115875995223506741)
          ·
            refine ⟨15629562010863374552203757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 166715328115875995223506741 15629562010863374552203757)
            ·
              refine ⟨5861085754073765457076409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15629562010863374552203757 5861085754073765457076409)
              ·
                refine ⟨4395814315555324092807307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5861085754073765457076409 4395814315555324092807307)
                ·
                  refine ⟨6593721473332986139210961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4395814315555324092807307 6593721473332986139210961)
                  ·
                    refine ⟨4945291104999739604408221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6593721473332986139210961 4945291104999739604408221)
                    ·
                      refine ⟨1854484164374902351653083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4945291104999739604408221 1854484164374902351653083)
                      ·
                        rfl

theorem cell23_3611595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 2, 1, 2, 3].length) (baseStart_3611595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3611595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3611595 prefixEnd_3611595 := by exact prefixLift 3611595
  have htrace : WordTrace (prefixWord ++ tailWord_3611595) baseStart_3611595 baseEnd_3611595 := by
    simpa [prefixWord, tailWord_3611595, baseEnd_3611595] using wordTrace_append hprefix tailTrace_3611595
  have hstable : (prefixWord ++ tailWord_3611595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611595).length < 2 ^ (prefixWord ++ tailWord_3611595).sum := by decide
  have hdescent : baseEnd_3611595 < baseStart_3611595 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611605 : List Nat := [1, 3, 2, 3, 3, 1, 1, 2, 1, 2, 4]
def baseStart_3611605 : Nat := 118140960795 + 3611605 * 2 ^ 59
def prefixEnd_3611605 : Nat := 4983230072969 + 3 ^ 40 * 3611605 * 2
def baseEnd_3611605 : Nat := 1854489299181447312528037

theorem tailTrace_3611605 : CollatzResearch.WordTrace tailWord_3611605 prefixEnd_3611605 1854489299181447312528037 := by
  unfold tailWord_3611605
  simp only [CollatzResearch.WordTrace]
  refine ⟨131726056080779372872116269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87817370720519581914744179 131726056080779372872116269)
  ·
    refine ⟨49397271030292264827043601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131726056080779372872116269 49397271030292264827043601)
    ·
      refine ⟨37047953272719198620282701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49397271030292264827043601 37047953272719198620282701)
      ·
        refine ⟨13892982477269699482606013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37047953272719198620282701 13892982477269699482606013)
        ·
          refine ⟨5209868428976137305977255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13892982477269699482606013 5209868428976137305977255)
          ·
            refine ⟨7814802643464205958965883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5209868428976137305977255 7814802643464205958965883)
            ·
              refine ⟨11722203965196308938448825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7814802643464205958965883 11722203965196308938448825)
              ·
                refine ⟨8791652973897231703836619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11722203965196308938448825 8791652973897231703836619)
                ·
                  refine ⟨13187479460845847555754929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8791652973897231703836619 13187479460845847555754929)
                  ·
                    refine ⟨9890609595634385666816197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13187479460845847555754929 9890609595634385666816197)
                    ·
                      refine ⟨1854489299181447312528037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9890609595634385666816197 1854489299181447312528037)
                      ·
                        rfl

theorem cell23_3611605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_3611605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3611605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3611605 prefixEnd_3611605 := by exact prefixLift 3611605
  have htrace : WordTrace (prefixWord ++ tailWord_3611605) baseStart_3611605 baseEnd_3611605 := by
    simpa [prefixWord, tailWord_3611605, baseEnd_3611605] using wordTrace_append hprefix tailTrace_3611605
  have hstable : (prefixWord ++ tailWord_3611605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611605).length < 2 ^ (prefixWord ++ tailWord_3611605).sum := by decide
  have hdescent : baseEnd_3611605 < baseStart_3611605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611608 : List Nat := [2, 1, 2, 2, 2, 3, 1, 1, 3, 3, 3]
def baseStart_3611608 : Nat := 118140960795 + 3611608 * 2 ^ 59
def prefixEnd_3611608 : Nat := 4983230072969 + 3 ^ 40 * 3611608 * 2
def baseEnd_3611608 : Nat := 1854490839623410800790523

theorem tailTrace_3611608 : CollatzResearch.WordTrace tailWord_3611608 prefixEnd_3611608 1854490839623410800790523 := by
  unfold tailWord_3611608
  simp only [CollatzResearch.WordTrace]
  refine ⟨65863082749884252192237739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87817443666512336256316985 65863082749884252192237739)
  ·
    refine ⟨98794624124826378288356609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65863082749884252192237739 98794624124826378288356609)
    ·
      refine ⟨74095968093619783716267457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98794624124826378288356609 74095968093619783716267457)
      ·
        refine ⟨55571976070214837787200593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74095968093619783716267457 55571976070214837787200593)
        ·
          refine ⟨41678982052661128340400445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55571976070214837787200593 41678982052661128340400445)
          ·
            refine ⟨15629618269747923127650167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41678982052661128340400445 15629618269747923127650167)
            ·
              refine ⟨23444427404621884691475251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15629618269747923127650167 23444427404621884691475251)
              ·
                refine ⟨35166641106932827037212877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23444427404621884691475251 35166641106932827037212877)
                ·
                  refine ⟨13187490415099810138954829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35166641106932827037212877 13187490415099810138954829)
                  ·
                    refine ⟨4945308905662428802108061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13187490415099810138954829 4945308905662428802108061)
                    ·
                      refine ⟨1854490839623410800790523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4945308905662428802108061 1854490839623410800790523)
                      ·
                        rfl

theorem cell23_3611608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 3, 3, 3].length) (baseStart_3611608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3611608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3611608 prefixEnd_3611608 := by exact prefixLift 3611608
  have htrace : WordTrace (prefixWord ++ tailWord_3611608) baseStart_3611608 baseEnd_3611608 := by
    simpa [prefixWord, tailWord_3611608, baseEnd_3611608] using wordTrace_append hprefix tailTrace_3611608
  have hstable : (prefixWord ++ tailWord_3611608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611608).length < 2 ^ (prefixWord ++ tailWord_3611608).sum := by decide
  have hdescent : baseEnd_3611608 < baseStart_3611608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611626 : List Nat := [3, 1, 3, 1, 2, 2, 4, 2, 1, 2, 2]
def baseStart_3611626 : Nat := 118140960795 + 3611626 * 2 ^ 59
def prefixEnd_3611626 : Nat := 4983230072969 + 3 ^ 40 * 3611626 * 2
def baseEnd_3611626 : Nat := 1854500082275191730365441

theorem tailTrace_3611626 : CollatzResearch.WordTrace tailWord_3611626 prefixEnd_3611626 1854500082275191730365441 := by
  unfold tailWord_3611626
  simp only [CollatzResearch.WordTrace]
  refine ⟨32931705503425823364657683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87817881342468862305753821 32931705503425823364657683)
  ·
    refine ⟨49397558255138735046986525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32931705503425823364657683 49397558255138735046986525)
    ·
      refine ⟨18524084345677025642619947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49397558255138735046986525 18524084345677025642619947)
      ·
        refine ⟨27786126518515538463929921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18524084345677025642619947 27786126518515538463929921)
        ·
          refine ⟨20839594888886653847947441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27786126518515538463929921 20839594888886653847947441)
          ·
            refine ⟨15629696166664990385960581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20839594888886653847947441 15629696166664990385960581)
            ·
              refine ⟨2930568031249685697367609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15629696166664990385960581 2930568031249685697367609)
              ·
                refine ⟨2197926023437264273025707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2930568031249685697367609 2197926023437264273025707)
                ·
                  refine ⟨3296889035155896409538561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2197926023437264273025707 3296889035155896409538561)
                  ·
                    refine ⟨2472666776366922307153921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3296889035155896409538561 2472666776366922307153921)
                    ·
                      refine ⟨1854500082275191730365441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2472666776366922307153921 1854500082275191730365441)
                      ·
                        rfl

theorem cell23_3611626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4, 2, 1, 2, 2].length) (baseStart_3611626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3611626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3611626 prefixEnd_3611626 := by exact prefixLift 3611626
  have htrace : WordTrace (prefixWord ++ tailWord_3611626) baseStart_3611626 baseEnd_3611626 := by
    simpa [prefixWord, tailWord_3611626, baseEnd_3611626] using wordTrace_append hprefix tailTrace_3611626
  have hstable : (prefixWord ++ tailWord_3611626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611626).length < 2 ^ (prefixWord ++ tailWord_3611626).sum := by decide
  have hdescent : baseEnd_3611626 < baseStart_3611626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611636 : List Nat := [2, 6, 2, 1, 1, 1, 2, 1, 1, 6]
def baseStart_3611636 : Nat := 118140960795 + 3611636 * 2 ^ 59
def prefixEnd_3611636 : Nat := 4983230072969 + 3 ^ 40 * 3611636 * 2
def baseEnd_3611636 : Nat := 618168405693912230413465

theorem tailTrace_3611636 : CollatzResearch.WordTrace tailWord_3611636 prefixEnd_3611636 618168405693912230413465 := by
  unfold tailWord_3611636
  simp only [CollatzResearch.WordTrace]
  refine ⟨65863593371833532583247381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87818124495778043444329841 65863593371833532583247381)
  ·
    refine ⟨3087355939304696839839721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 65863593371833532583247381 3087355939304696839839721)
    ·
      refine ⟨2315516954478522629879791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3087355939304696839839721 2315516954478522629879791)
      ·
        refine ⟨3473275431717783944819687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2315516954478522629879791 3473275431717783944819687)
        ·
          refine ⟨5209913147576675917229531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3473275431717783944819687 5209913147576675917229531)
          ·
            refine ⟨7814869721365013875844297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5209913147576675917229531 7814869721365013875844297)
            ·
              refine ⟨5861152291023760406883223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7814869721365013875844297 5861152291023760406883223)
              ·
                refine ⟨8791728436535640610324835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5861152291023760406883223 8791728436535640610324835)
                ·
                  refine ⟨13187592654803460915487253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8791728436535640610324835 13187592654803460915487253)
                  ·
                    refine ⟨618168405693912230413465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13187592654803460915487253 618168405693912230413465)
                    ·
                      rfl

theorem cell23_3611636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_3611636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3611636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3611636 prefixEnd_3611636 := by exact prefixLift 3611636
  have htrace : WordTrace (prefixWord ++ tailWord_3611636) baseStart_3611636 baseEnd_3611636 := by
    simpa [prefixWord, tailWord_3611636, baseEnd_3611636] using wordTrace_append hprefix tailTrace_3611636
  have hstable : (prefixWord ++ tailWord_3611636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611636).length < 2 ^ (prefixWord ++ tailWord_3611636).sum := by decide
  have hdescent : baseEnd_3611636 < baseStart_3611636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611669 : List Nat := [1, 3, 2, 1, 4, 1, 4, 1, 1, 3, 2]
def baseStart_3611669 : Nat := 118140960795 + 3611669 * 2 ^ 59
def prefixEnd_3611669 : Nat := 4983230072969 + 3 ^ 40 * 3611669 * 2
def baseEnd_3611669 : Nat := 1854522161943335062127743

theorem tailTrace_3611669 : CollatzResearch.WordTrace tailWord_3611669 prefixEnd_3611669 1854522161943335062127743 := by
  unfold tailWord_3611669
  simp only [CollatzResearch.WordTrace]
  refine ⟨131728390352547511802446061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87818926901698341201630707 131728390352547511802446061)
  ·
    refine ⟨49398146382205316925917273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131728390352547511802446061 49398146382205316925917273)
    ·
      refine ⟨37048609786653987694437955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49398146382205316925917273 37048609786653987694437955)
      ·
        refine ⟨55572914679980981541656933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37048609786653987694437955 55572914679980981541656933)
        ·
          refine ⟨10419921502496434039060675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55572914679980981541656933 10419921502496434039060675)
          ·
            refine ⟨15629882253744651058591013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10419921502496434039060675 15629882253744651058591013)
            ·
              refine ⟨2930602922577122073485815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15629882253744651058591013 2930602922577122073485815)
              ·
                refine ⟨4395904383865683110228723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2930602922577122073485815 4395904383865683110228723)
                ·
                  refine ⟨6593856575798524665343085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4395904383865683110228723 6593856575798524665343085)
                  ·
                    refine ⟨2472696215924446749503657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6593856575798524665343085 2472696215924446749503657)
                    ·
                      refine ⟨1854522161943335062127743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2472696215924446749503657 1854522161943335062127743)
                      ·
                        rfl

theorem cell23_3611669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4, 1, 1, 3, 2].length) (baseStart_3611669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3611669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3611669 prefixEnd_3611669 := by exact prefixLift 3611669
  have htrace : WordTrace (prefixWord ++ tailWord_3611669) baseStart_3611669 baseEnd_3611669 := by
    simpa [prefixWord, tailWord_3611669, baseEnd_3611669] using wordTrace_append hprefix tailTrace_3611669
  have hstable : (prefixWord ++ tailWord_3611669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611669).length < 2 ^ (prefixWord ++ tailWord_3611669).sum := by decide
  have hdescent : baseEnd_3611669 < baseStart_3611669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611676 : List Nat := [2, 2, 3, 1, 5, 1, 1, 2, 2, 1, 3]
def baseStart_3611676 : Nat := 118140960795 + 3611676 * 2 ^ 59
def prefixEnd_3611676 : Nat := 4983230072969 + 3 ^ 40 * 3611676 * 2
def baseEnd_3611676 : Nat := 1854525756307916534740211

theorem tailTrace_3611676 : CollatzResearch.WordTrace tailWord_3611676 prefixEnd_3611676 1854525756307916534740211 := by
  unfold tailWord_3611676
  simp only [CollatzResearch.WordTrace]
  refine ⟨65864322831761075998975441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87819097109014767998633921 65864322831761075998975441)
  ·
    refine ⟨49398242123820806999231581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65864322831761075998975441 49398242123820806999231581)
    ·
      refine ⟨18524340796432802624711843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49398242123820806999231581 18524340796432802624711843)
      ·
        refine ⟨27786511194649203937067765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18524340796432802624711843 27786511194649203937067765)
        ·
          refine ⟨2604985424498362869100103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27786511194649203937067765 2604985424498362869100103)
          ·
            refine ⟨3907478136747544303650155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2604985424498362869100103 3907478136747544303650155)
            ·
              refine ⟨5861217205121316455475233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3907478136747544303650155 5861217205121316455475233)
              ·
                refine ⟨4395912903840987341606425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5861217205121316455475233 4395912903840987341606425)
                ·
                  refine ⟨3296934677880740506204819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4395912903840987341606425 3296934677880740506204819)
                  ·
                    refine ⟨4945402016821110759307229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3296934677880740506204819 4945402016821110759307229)
                    ·
                      refine ⟨1854525756307916534740211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4945402016821110759307229 1854525756307916534740211)
                      ·
                        rfl

theorem cell23_3611676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 2, 2, 1, 3].length) (baseStart_3611676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3611676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3611676 prefixEnd_3611676 := by exact prefixLift 3611676
  have htrace : WordTrace (prefixWord ++ tailWord_3611676) baseStart_3611676 baseEnd_3611676 := by
    simpa [prefixWord, tailWord_3611676, baseEnd_3611676] using wordTrace_append hprefix tailTrace_3611676
  have hstable : (prefixWord ++ tailWord_3611676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611676).length < 2 ^ (prefixWord ++ tailWord_3611676).sum := by decide
  have hdescent : baseEnd_3611676 < baseStart_3611676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611738 : List Nat := [3, 1, 1, 2, 1, 1, 2, 2, 3, 3, 4]
def baseStart_3611738 : Nat := 118140960795 + 3611738 * 2 ^ 59
def prefixEnd_3611738 : Nat := 4983230072969 + 3 ^ 40 * 3611738 * 2
def baseEnd_3611738 : Nat := 1854557592108495292164925

theorem tailTrace_3611738 : CollatzResearch.WordTrace tailWord_3611738 prefixEnd_3611738 1854557592108495292164925 := by
  unfold tailWord_3611738
  simp only [CollatzResearch.WordTrace]
  refine ⟨32932726747324384146676967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87820604659531691057805245 32932726747324384146676967)
  ·
    refine ⟨49399090120986576220015451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32932726747324384146676967 49399090120986576220015451)
    ·
      refine ⟨74098635181479864330023177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49399090120986576220015451 74098635181479864330023177)
      ·
        refine ⟨55573976386109898247517383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74098635181479864330023177 55573976386109898247517383)
        ·
          refine ⟨83360964579164847371276075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55573976386109898247517383 83360964579164847371276075)
          ·
            refine ⟨125041446868747271056914113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83360964579164847371276075 125041446868747271056914113)
            ·
              refine ⟨93781085151560453292685585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125041446868747271056914113 93781085151560453292685585)
              ·
                refine ⟨70335813863670339969514189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93781085151560453292685585 70335813863670339969514189)
                ·
                  refine ⟨26375930198876377488567821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70335813863670339969514189 26375930198876377488567821)
                  ·
                    refine ⟨9890973824578641558212933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26375930198876377488567821 9890973824578641558212933)
                    ·
                      refine ⟨1854557592108495292164925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9890973824578641558212933 1854557592108495292164925)
                      ·
                        rfl

theorem cell23_3611738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_3611738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3611738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3611738 prefixEnd_3611738 := by exact prefixLift 3611738
  have htrace : WordTrace (prefixWord ++ tailWord_3611738) baseStart_3611738 baseEnd_3611738 := by
    simpa [prefixWord, tailWord_3611738, baseEnd_3611738] using wordTrace_append hprefix tailTrace_3611738
  have hstable : (prefixWord ++ tailWord_3611738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611738).length < 2 ^ (prefixWord ++ tailWord_3611738).sum := by decide
  have hdescent : baseEnd_3611738 < baseStart_3611738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611768 : List Nat := [2, 1, 2, 1, 1, 1, 4, 1, 2, 4, 4]
def baseStart_3611768 : Nat := 118140960795 + 3611768 * 2 ^ 59
def prefixEnd_3611768 : Nat := 4983230072969 + 3 ^ 40 * 3611768 * 2
def baseEnd_3611768 : Nat := 1854572996528130174789787

theorem tailTrace_3611768 : CollatzResearch.WordTrace tailWord_3611768 prefixEnd_3611768 1854572996528130174789787 := by
  unfold tailWord_3611768
  simp only [CollatzResearch.WordTrace]
  refine ⟨65866000589594425855149979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87821334119459234473533305 65866000589594425855149979)
  ·
    refine ⟨98799000884391638782724969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65866000589594425855149979 98799000884391638782724969)
    ·
      refine ⟨74099250663293729087043727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98799000884391638782724969 74099250663293729087043727)
      ·
        refine ⟨111148875994940593630565591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74099250663293729087043727 111148875994940593630565591)
        ·
          refine ⟨166723313992410890445848387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111148875994940593630565591 166723313992410890445848387)
          ·
            refine ⟨250084970988616335668772581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166723313992410890445848387 250084970988616335668772581)
            ·
              refine ⟨46890932060365562937894859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 250084970988616335668772581 46890932060365562937894859)
              ·
                refine ⟨70336398090548344406842289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46890932060365562937894859 70336398090548344406842289)
                ·
                  refine ⟨52752298567911258305131717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70336398090548344406842289 52752298567911258305131717)
                  ·
                    refine ⟨9891055981483360932212197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52752298567911258305131717 9891055981483360932212197)
                    ·
                      refine ⟨1854572996528130174789787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9891055981483360932212197 1854572996528130174789787)
                      ·
                        rfl

theorem cell23_3611768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 2, 4, 4].length) (baseStart_3611768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3611768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3611768 prefixEnd_3611768 := by exact prefixLift 3611768
  have htrace : WordTrace (prefixWord ++ tailWord_3611768) baseStart_3611768 baseEnd_3611768 := by
    simpa [prefixWord, tailWord_3611768, baseEnd_3611768] using wordTrace_append hprefix tailTrace_3611768
  have hstable : (prefixWord ++ tailWord_3611768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611768).length < 2 ^ (prefixWord ++ tailWord_3611768).sum := by decide
  have hdescent : baseEnd_3611768 < baseStart_3611768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611799 : List Nat := [1, 1, 3, 3, 3, 2, 1, 4, 1, 4]
def baseStart_3611799 : Nat := 118140960795 + 3611799 * 2 ^ 59
def prefixEnd_3611799 : Nat := 4983230072969 + 3 ^ 40 * 3611799 * 2
def baseEnd_3611799 : Nat := 618196304809473184500715

theorem tailTrace_3611799 : CollatzResearch.WordTrace tailWord_3611799 prefixEnd_3611799 618196304809473184500715 := by
  unfold tailWord_3611799
  simp only [CollatzResearch.WordTrace]
  refine ⟨131733131842076544004678451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87822087894717696003118967 131733131842076544004678451)
  ·
    refine ⟨197599697763114816007017677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131733131842076544004678451 197599697763114816007017677)
    ·
      refine ⟨74099886661168056002631629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197599697763114816007017677 74099886661168056002631629)
      ·
        refine ⟨27787457497938021000986861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74099886661168056002631629 27787457497938021000986861)
        ·
          refine ⟨10420296561726757875370073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27787457497938021000986861 10420296561726757875370073)
          ·
            refine ⟨7815222421295068406527555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10420296561726757875370073 7815222421295068406527555)
            ·
              refine ⟨11722833631942602609791333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7815222421295068406527555 11722833631942602609791333)
              ·
                refine ⟨2198031305989237989335875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11722833631942602609791333 2198031305989237989335875)
                ·
                  refine ⟨3297046958983856984003813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2198031305989237989335875 3297046958983856984003813)
                  ·
                    refine ⟨618196304809473184500715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3297046958983856984003813 618196304809473184500715)
                    ·
                      rfl

theorem cell23_3611799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 4, 1, 4].length) (baseStart_3611799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3611799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3611799 prefixEnd_3611799 := by exact prefixLift 3611799
  have htrace : WordTrace (prefixWord ++ tailWord_3611799) baseStart_3611799 baseEnd_3611799 := by
    simpa [prefixWord, tailWord_3611799, baseEnd_3611799] using wordTrace_append hprefix tailTrace_3611799
  have hstable : (prefixWord ++ tailWord_3611799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611799).length < 2 ^ (prefixWord ++ tailWord_3611799).sum := by decide
  have hdescent : baseEnd_3611799 < baseStart_3611799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611832 : List Nat := [2, 1, 2, 1, 2, 1, 2, 5, 2, 3, 2]
def baseStart_3611832 : Nat := 118140960795 + 3611832 * 2 ^ 59
def prefixEnd_3611832 : Nat := 4983230072969 + 3 ^ 40 * 3611832 * 2
def baseEnd_3611832 : Nat := 1854605859290017924389493

theorem tailTrace_3611832 : CollatzResearch.WordTrace tailWord_3611832 prefixEnd_3611832 1854605859290017924389493 := by
  unfold tailWord_3611832
  simp only [CollatzResearch.WordTrace]
  refine ⟨65867167725478495320314875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87822890300637993760419833 65867167725478495320314875)
  ·
    refine ⟨98800751588217742980472313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65867167725478495320314875 98800751588217742980472313)
    ·
      refine ⟨74100563691163307235354235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98800751588217742980472313 74100563691163307235354235)
      ·
        refine ⟨111150845536744960853031353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74100563691163307235354235 111150845536744960853031353)
        ·
          refine ⟨83363134152558720639773515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111150845536744960853031353 83363134152558720639773515)
          ·
            refine ⟨125044701228838080959660273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83363134152558720639773515 125044701228838080959660273)
            ·
              refine ⟨93783525921628560719745205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125044701228838080959660273 93783525921628560719745205)
              ·
                refine ⟨8792205555152677567476113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93783525921628560719745205 8792205555152677567476113)
                ·
                  refine ⟨6594154166364508175607085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8792205555152677567476113 6594154166364508175607085)
                  ·
                    refine ⟨2472807812386690565852657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6594154166364508175607085 2472807812386690565852657)
                    ·
                      refine ⟨1854605859290017924389493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2472807812386690565852657 1854605859290017924389493)
                      ·
                        rfl

theorem cell23_3611832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5, 2, 3, 2].length) (baseStart_3611832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3611832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3611832 prefixEnd_3611832 := by exact prefixLift 3611832
  have htrace : WordTrace (prefixWord ++ tailWord_3611832) baseStart_3611832 baseEnd_3611832 := by
    simpa [prefixWord, tailWord_3611832, baseEnd_3611832] using wordTrace_append hprefix tailTrace_3611832
  have hstable : (prefixWord ++ tailWord_3611832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611832).length < 2 ^ (prefixWord ++ tailWord_3611832).sum := by decide
  have hdescent : baseEnd_3611832 < baseStart_3611832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611839 : List Nat := [1, 1, 2, 2, 2, 2, 3, 5, 1, 1, 3]
def baseStart_3611839 : Nat := 118140960795 + 3611839 * 2 ^ 59
def prefixEnd_3611839 : Nat := 4983230072969 + 3 ^ 40 * 3611839 * 2
def baseEnd_3611839 : Nat := 1854609453654599397001961

theorem tailTrace_3611839 : CollatzResearch.WordTrace tailWord_3611839 prefixEnd_3611839 1854609453654599397001961 := by
  unfold tailWord_3611839
  simp only [CollatzResearch.WordTrace]
  refine ⟨131734590761931630836134571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87823060507954420557423047 131734590761931630836134571)
  ·
    refine ⟨197601886142897446254201857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131734590761931630836134571 197601886142897446254201857)
    ·
      refine ⟨148201414607173084690651393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197601886142897446254201857 148201414607173084690651393)
      ·
        refine ⟨111151060955379813517988545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148201414607173084690651393 111151060955379813517988545)
        ·
          refine ⟨83363295716534860138491409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111151060955379813517988545 83363295716534860138491409)
          ·
            refine ⟨62522471787401145103868557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83363295716534860138491409 62522471787401145103868557)
            ·
              refine ⟨23445926920275429413950709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62522471787401145103868557 23445926920275429413950709)
              ·
                refine ⟨2198055648775821507557879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23445926920275429413950709 2198055648775821507557879)
                ·
                  refine ⟨3297083473163732261336819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2198055648775821507557879 3297083473163732261336819)
                  ·
                    refine ⟨4945625209745598392005229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3297083473163732261336819 4945625209745598392005229)
                    ·
                      refine ⟨1854609453654599397001961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4945625209745598392005229 1854609453654599397001961)
                      ·
                        rfl

theorem cell23_3611839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 5, 1, 1, 3].length) (baseStart_3611839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3611839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3611839 prefixEnd_3611839 := by exact prefixLift 3611839
  have htrace : WordTrace (prefixWord ++ tailWord_3611839) baseStart_3611839 baseEnd_3611839 := by
    simpa [prefixWord, tailWord_3611839, baseEnd_3611839] using wordTrace_append hprefix tailTrace_3611839
  have hstable : (prefixWord ++ tailWord_3611839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611839).length < 2 ^ (prefixWord ++ tailWord_3611839).sum := by decide
  have hdescent : baseEnd_3611839 < baseStart_3611839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611846 : List Nat := [6, 1, 2, 2, 1, 1, 1, 1, 8]
def baseStart_3611846 : Nat := 118140960795 + 3611846 * 2 ^ 59
def prefixEnd_3611846 : Nat := 4983230072969 + 3 ^ 40 * 3611846 * 2
def baseEnd_3611846 : Nat := 206068116446575652179381

theorem tailTrace_3611846 : CollatzResearch.WordTrace tailWord_3611846 prefixEnd_3611846 206068116446575652179381 := by
  unfold tailWord_3611846
  simp only [CollatzResearch.WordTrace]
  refine ⟨4116713939778320969738731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 87823230715270847354426261 4116713939778320969738731)
  ·
    refine ⟨6175070909667481454608097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4116713939778320969738731 6175070909667481454608097)
    ·
      refine ⟨4631303182250611090956073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6175070909667481454608097 4631303182250611090956073)
      ·
        refine ⟨3473477386687958318217055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4631303182250611090956073 3473477386687958318217055)
        ·
          refine ⟨5210216080031937477325583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3473477386687958318217055 5210216080031937477325583)
          ·
            refine ⟨7815324120047906215988375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5210216080031937477325583 7815324120047906215988375)
            ·
              refine ⟨11722986180071859323982563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7815324120047906215988375 11722986180071859323982563)
              ·
                refine ⟨17584479270107788985973845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11722986180071859323982563 17584479270107788985973845)
                ·
                  refine ⟨206068116446575652179381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17584479270107788985973845 206068116446575652179381)
                  ·
                    rfl

theorem cell23_3611846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_3611846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3611846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3611846 prefixEnd_3611846 := by exact prefixLift 3611846
  have htrace : WordTrace (prefixWord ++ tailWord_3611846) baseStart_3611846 baseEnd_3611846 := by
    simpa [prefixWord, tailWord_3611846, baseEnd_3611846] using wordTrace_append hprefix tailTrace_3611846
  have hstable : (prefixWord ++ tailWord_3611846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611846).length < 2 ^ (prefixWord ++ tailWord_3611846).sum := by decide
  have hdescent : baseEnd_3611846 < baseStart_3611846 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611872 : List Nat := [2, 1, 1, 3, 1, 6, 1, 1, 1, 6]
def baseStart_3611872 : Nat := 118140960795 + 3611872 * 2 ^ 59
def prefixEnd_3611872 : Nat := 4983230072969 + 3 ^ 40 * 3611872 * 2
def baseEnd_3611872 : Nat := 618208799505399255963103

theorem tailTrace_3611872 : CollatzResearch.WordTrace tailWord_3611872 prefixEnd_3611872 618208799505399255963103 := by
  unfold tailWord_3611872
  simp only [CollatzResearch.WordTrace]
  refine ⟨65867897185406038736042935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87823862913874718314723913 65867897185406038736042935)
  ·
    refine ⟨98801845778109058104064403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65867897185406038736042935 98801845778109058104064403)
    ·
      refine ⟨148202768667163587156096605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98801845778109058104064403 148202768667163587156096605)
      ·
        refine ⟨55576038250186345183536227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148202768667163587156096605 55576038250186345183536227)
        ·
          refine ⟨83364057375279517775304341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55576038250186345183536227 83364057375279517775304341)
          ·
            refine ⟨3907690189466227395717391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 83364057375279517775304341 3907690189466227395717391)
            ·
              refine ⟨5861535284199341093576087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3907690189466227395717391 5861535284199341093576087)
              ·
                refine ⟨8792302926299011640364131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5861535284199341093576087 8792302926299011640364131)
                ·
                  refine ⟨13188454389448517460546197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8792302926299011640364131 13188454389448517460546197)
                  ·
                    refine ⟨618208799505399255963103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13188454389448517460546197 618208799505399255963103)
                    ·
                      rfl

theorem cell23_3611872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 1, 1, 6].length) (baseStart_3611872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3611872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3611872 prefixEnd_3611872 := by exact prefixLift 3611872
  have htrace : WordTrace (prefixWord ++ tailWord_3611872) baseStart_3611872 baseEnd_3611872 := by
    simpa [prefixWord, tailWord_3611872, baseEnd_3611872] using wordTrace_append hprefix tailTrace_3611872
  have hstable : (prefixWord ++ tailWord_3611872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611872).length < 2 ^ (prefixWord ++ tailWord_3611872).sum := by decide
  have hdescent : baseEnd_3611872 < baseStart_3611872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611890 : List Nat := [3, 2, 1, 3, 4, 1, 1, 3, 1, 1, 3]
def baseStart_3611890 : Nat := 118140960795 + 3611890 * 2 ^ 59
def prefixEnd_3611890 : Nat := 4983230072969 + 3 ^ 40 * 3611890 * 2
def baseEnd_3611890 : Nat := 1854635641167978697464227

theorem tailTrace_3611890 : CollatzResearch.WordTrace tailWord_3611890 prefixEnd_3611890 1854635641167978697464227 := by
  unfold tailWord_3611890
  simp only [CollatzResearch.WordTrace]
  refine ⟨32934112721186716636560281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87824300589831244364160749 32934112721186716636560281)
  ·
    refine ⟨24700584540890037477420211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32934112721186716636560281 24700584540890037477420211)
    ·
      refine ⟨37050876811335056216130317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24700584540890037477420211 37050876811335056216130317)
      ·
        refine ⟨13894078804250646081048869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37050876811335056216130317 13894078804250646081048869)
        ·
          refine ⟨2605139775796996140196663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13894078804250646081048869 2605139775796996140196663)
          ·
            refine ⟨3907709663695494210294995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2605139775796996140196663 3907709663695494210294995)
            ·
              refine ⟨5861564495543241315442493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3907709663695494210294995 5861564495543241315442493)
              ·
                refine ⟨2198086685828715493290935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5861564495543241315442493 2198086685828715493290935)
                ·
                  refine ⟨3297130028743073239936403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2198086685828715493290935 3297130028743073239936403)
                  ·
                    refine ⟨4945695043114609859904605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3297130028743073239936403 4945695043114609859904605)
                    ·
                      refine ⟨1854635641167978697464227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4945695043114609859904605 1854635641167978697464227)
                      ·
                        rfl

theorem cell23_3611890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_3611890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3611890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3611890 prefixEnd_3611890 := by exact prefixLift 3611890
  have htrace : WordTrace (prefixWord ++ tailWord_3611890) baseStart_3611890 baseEnd_3611890 := by
    simpa [prefixWord, tailWord_3611890, baseEnd_3611890] using wordTrace_append hprefix tailTrace_3611890
  have hstable : (prefixWord ++ tailWord_3611890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611890).length < 2 ^ (prefixWord ++ tailWord_3611890).sum := by decide
  have hdescent : baseEnd_3611890 < baseStart_3611890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611902 : List Nat := [4, 2, 2, 1, 1, 4, 9]
def baseStart_3611902 : Nat := 118140960795 + 3611902 * 2 ^ 59
def prefixEnd_3611902 : Nat := 4983230072969 + 3 ^ 40 * 3611902 * 2
def baseEnd_3611902 : Nat := 22896812381923859882891

theorem tailTrace_3611902 : CollatzResearch.WordTrace tailWord_3611902 prefixEnd_3611902 22896812381923859882891 := by
  unfold tailWord_3611902
  simp only [CollatzResearch.WordTrace]
  refine ⟨16467111070087924074459745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87824592373802261730451973 16467111070087924074459745)
  ·
    refine ⟨12350333302565943055844809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16467111070087924074459745 12350333302565943055844809)
    ·
      refine ⟨9262749976924457291883607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12350333302565943055844809 9262749976924457291883607)
      ·
        refine ⟨13894124965386685937825411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9262749976924457291883607 13894124965386685937825411)
        ·
          refine ⟨20841187448080028906738117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13894124965386685937825411 20841187448080028906738117)
          ·
            refine ⟨3907722646515005420013397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20841187448080028906738117 3907722646515005420013397)
            ·
              refine ⟨22896812381923859882891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3907722646515005420013397 22896812381923859882891)
              ·
                rfl

theorem cell23_3611902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 9].length) (baseStart_3611902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3611902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3611902 prefixEnd_3611902 := by exact prefixLift 3611902
  have htrace : WordTrace (prefixWord ++ tailWord_3611902) baseStart_3611902 baseEnd_3611902 := by
    simpa [prefixWord, tailWord_3611902, baseEnd_3611902] using wordTrace_append hprefix tailTrace_3611902
  have hstable : (prefixWord ++ tailWord_3611902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611902).length < 2 ^ (prefixWord ++ tailWord_3611902).sum := by decide
  have hdescent : baseEnd_3611902 < baseStart_3611902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611913 : List Nat := [1, 2, 1, 1, 3, 3, 5, 2, 1, 2, 2]
def baseStart_3611913 : Nat := 118140960795 + 3611913 * 2 ^ 59
def prefixEnd_3611913 : Nat := 4983230072969 + 3 ^ 40 * 3611913 * 2
def baseEnd_3611913 : Nat := 1854647451223032107476621

theorem tailTrace_3611913 : CollatzResearch.WordTrace tailWord_3611913 prefixEnd_3611913 1854647451223032107476621 := by
  unfold tailWord_3611913
  simp only [CollatzResearch.WordTrace]
  refine ⟨131737289763663541474328393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87824859842442360982885595 131737289763663541474328393)
  ·
    refine ⟨98802967322747656105746295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131737289763663541474328393 98802967322747656105746295)
    ·
      refine ⟨148204450984121484158619443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98802967322747656105746295 148204450984121484158619443)
      ·
        refine ⟨222306676476182226237929165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148204450984121484158619443 222306676476182226237929165)
        ·
          refine ⟨83365003678568334839223437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222306676476182226237929165 83365003678568334839223437)
          ·
            refine ⟨31261876379463125564708789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83365003678568334839223437 31261876379463125564708789)
            ·
              refine ⟨2930800910574668021691449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31261876379463125564708789 2930800910574668021691449)
              ·
                refine ⟨2198100682931001016268587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2930800910574668021691449 2198100682931001016268587)
                ·
                  refine ⟨3297151024396501524402881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2198100682931001016268587 3297151024396501524402881)
                  ·
                    refine ⟨2472863268297376143302161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3297151024396501524402881 2472863268297376143302161)
                    ·
                      refine ⟨1854647451223032107476621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2472863268297376143302161 1854647451223032107476621)
                      ·
                        rfl

theorem cell23_3611913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5, 2, 1, 2, 2].length) (baseStart_3611913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3611913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3611913 prefixEnd_3611913 := by exact prefixLift 3611913
  have htrace : WordTrace (prefixWord ++ tailWord_3611913) baseStart_3611913 baseEnd_3611913 := by
    simpa [prefixWord, tailWord_3611913, baseEnd_3611913] using wordTrace_append hprefix tailTrace_3611913
  have hstable : (prefixWord ++ tailWord_3611913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611913).length < 2 ^ (prefixWord ++ tailWord_3611913).sum := by decide
  have hdescent : baseEnd_3611913 < baseStart_3611913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611939 : List Nat := [1, 1, 1, 4, 2, 4, 1, 1, 3, 3, 2]
def baseStart_3611939 : Nat := 118140960795 + 3611939 * 2 ^ 59
def prefixEnd_3611939 : Nat := 4983230072969 + 3 ^ 40 * 3611939 * 2
def baseEnd_3611939 : Nat := 1854660801720049005751501

theorem tailTrace_3611939 : CollatzResearch.WordTrace tailWord_3611939 prefixEnd_3611939 1854660801720049005751501 := by
  unfold tailWord_3611939
  simp only [CollatzResearch.WordTrace]
  refine ⟨131738238061569347914774871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87825492041046231943183247 131738238061569347914774871)
  ·
    refine ⟨197607357092354021872162307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131738238061569347914774871 197607357092354021872162307)
    ·
      refine ⟨296411035638531032808243461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197607357092354021872162307 296411035638531032808243461)
      ·
        refine ⟨55577069182224568651545649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 296411035638531032808243461 55577069182224568651545649)
        ·
          refine ⟨41682801886668426488659237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55577069182224568651545649 41682801886668426488659237)
          ·
            refine ⟨7815525353750329966623607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41682801886668426488659237 7815525353750329966623607)
            ·
              refine ⟨11723288030625494949935411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7815525353750329966623607 11723288030625494949935411)
              ·
                refine ⟨17584932045938242424903117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11723288030625494949935411 17584932045938242424903117)
                ·
                  refine ⟨6594349517226840909338669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17584932045938242424903117 6594349517226840909338669)
                  ·
                    refine ⟨2472881068960065341002001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6594349517226840909338669 2472881068960065341002001)
                    ·
                      refine ⟨1854660801720049005751501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2472881068960065341002001 1854660801720049005751501)
                      ·
                        rfl

theorem cell23_3611939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 3, 3, 2].length) (baseStart_3611939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3611939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3611939 prefixEnd_3611939 := by exact prefixLift 3611939
  have htrace : WordTrace (prefixWord ++ tailWord_3611939) baseStart_3611939 baseEnd_3611939 := by
    simpa [prefixWord, tailWord_3611939, baseEnd_3611939] using wordTrace_append hprefix tailTrace_3611939
  have hstable : (prefixWord ++ tailWord_3611939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611939).length < 2 ^ (prefixWord ++ tailWord_3611939).sum := by decide
  have hdescent : baseEnd_3611939 < baseStart_3611939 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3611982 : List Nat := [4, 1, 1, 1, 1, 1, 5, 1, 2, 2, 4]
def baseStart_3611982 : Nat := 118140960795 + 3611982 * 2 ^ 59
def prefixEnd_3611982 : Nat := 4983230072969 + 3 ^ 40 * 3611982 * 2
def baseEnd_3611982 : Nat := 1854682881388192337513803

theorem tailTrace_3611982 : CollatzResearch.WordTrace tailWord_3611982 prefixEnd_3611982 1854682881388192337513803 := by
  unfold tailWord_3611982
  simp only [CollatzResearch.WordTrace]
  refine ⟨16467475800051695782323775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87826537600275710839060133 16467475800051695782323775)
  ·
    refine ⟨24701213700077543673485663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16467475800051695782323775 24701213700077543673485663)
    ·
      refine ⟨37051820550116315510228495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24701213700077543673485663 37051820550116315510228495)
      ·
        refine ⟨55577730825174473265342743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37051820550116315510228495 55577730825174473265342743)
        ·
          refine ⟨83366596237761709898014115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55577730825174473265342743 83366596237761709898014115)
          ·
            refine ⟨125049894356642564847021173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83366596237761709898014115 125049894356642564847021173)
            ·
              refine ⟨11723427595935240454408235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 125049894356642564847021173 11723427595935240454408235)
              ·
                refine ⟨17585141393902860681612353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11723427595935240454408235 17585141393902860681612353)
                ·
                  refine ⟨13188856045427145511209265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17585141393902860681612353 13188856045427145511209265)
                  ·
                    refine ⟨9891642034070359133406949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13188856045427145511209265 9891642034070359133406949)
                    ·
                      refine ⟨1854682881388192337513803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9891642034070359133406949 1854682881388192337513803)
                      ·
                        rfl

theorem cell23_3611982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_3611982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3611982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3611982 prefixEnd_3611982 := by exact prefixLift 3611982
  have htrace : WordTrace (prefixWord ++ tailWord_3611982) baseStart_3611982 baseEnd_3611982 := by
    simpa [prefixWord, tailWord_3611982, baseEnd_3611982] using wordTrace_append hprefix tailTrace_3611982
  have hstable : (prefixWord ++ tailWord_3611982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3611982).length < 2 ^ (prefixWord ++ tailWord_3611982).sum := by decide
  have hdescent : baseEnd_3611982 < baseStart_3611982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3611982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612060 : List Nat := [2, 2, 3, 4, 2, 1, 1, 3, 5]
def baseStart_3612060 : Nat := 118140960795 + 3612060 * 2 ^ 59
def prefixEnd_3612060 : Nat := 4983230072969 + 3 ^ 40 * 3612060 * 2
def baseEnd_3612060 : Nat := 206080325875471448037605

theorem tailTrace_3612060 : CollatzResearch.WordTrace tailWord_3612060 prefixEnd_3612060 206080325875471448037605 := by
  unfold tailWord_3612060
  simp only [CollatzResearch.WordTrace]
  refine ⟨65871325647065492789964817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87828434196087323719953089 65871325647065492789964817)
  ·
    refine ⟨49403494235299119592473613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65871325647065492789964817 49403494235299119592473613)
    ·
      refine ⟨18526310338237169847177605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49403494235299119592473613 18526310338237169847177605)
      ·
        refine ⟨3473683188419469346345801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18526310338237169847177605 3473683188419469346345801)
        ·
          refine ⟨2605262391314602009759351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3473683188419469346345801 2605262391314602009759351)
          ·
            refine ⟨3907893586971903014639027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2605262391314602009759351 3907893586971903014639027)
            ·
              refine ⟨5861840380457854521958541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3907893586971903014639027 5861840380457854521958541)
              ·
                refine ⟨2198190142671695445734453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5861840380457854521958541 2198190142671695445734453)
                ·
                  refine ⟨206080325875471448037605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2198190142671695445734453 206080325875471448037605)
                  ·
                    rfl

theorem cell23_3612060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 3, 5].length) (baseStart_3612060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3612060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3612060 prefixEnd_3612060 := by exact prefixLift 3612060
  have htrace : WordTrace (prefixWord ++ tailWord_3612060) baseStart_3612060 baseEnd_3612060 := by
    simpa [prefixWord, tailWord_3612060, baseEnd_3612060] using wordTrace_append hprefix tailTrace_3612060
  have hstable : (prefixWord ++ tailWord_3612060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612060).length < 2 ^ (prefixWord ++ tailWord_3612060).sum := by decide
  have hdescent : baseEnd_3612060 < baseStart_3612060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612099 : List Nat := [1, 1, 1, 3, 1, 1, 8, 1, 6]
def baseStart_3612099 : Nat := 118140960795 + 3612099 * 2 ^ 59
def prefixEnd_3612099 : Nat := 4983230072969 + 3 ^ 40 * 3612099 * 2
def baseEnd_3612099 : Nat := 206082550958307597750085

theorem tailTrace_3612099 : CollatzResearch.WordTrace tailWord_3612099 prefixEnd_3612099 206082550958307597750085 := by
  unfold tailWord_3612099
  simp only [CollatzResearch.WordTrace]
  refine ⟨131744073740989695240599351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87829382493993130160399567 131744073740989695240599351)
  ·
    refine ⟨197616110611484542860899027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131744073740989695240599351 197616110611484542860899027)
    ·
      refine ⟨296424165917226814291348541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197616110611484542860899027 296424165917226814291348541)
      ·
        refine ⟨111159062218960055359255703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 296424165917226814291348541 111159062218960055359255703)
        ·
          refine ⟨166738593328440083038883555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111159062218960055359255703 166738593328440083038883555)
          ·
            refine ⟨250107889992660124558325333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166738593328440083038883555 250107889992660124558325333)
            ·
              refine ⟨2930951835851485834667875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 250107889992660124558325333 2930951835851485834667875)
              ·
                refine ⟨4396427753777228752001813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2930951835851485834667875 4396427753777228752001813)
                ·
                  refine ⟨206082550958307597750085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4396427753777228752001813 206082550958307597750085)
                  ·
                    rfl

theorem cell23_3612099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8, 1, 6].length) (baseStart_3612099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3612099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3612099 prefixEnd_3612099 := by exact prefixLift 3612099
  have htrace : WordTrace (prefixWord ++ tailWord_3612099) baseStart_3612099 baseEnd_3612099 := by
    simpa [prefixWord, tailWord_3612099, baseEnd_3612099] using wordTrace_append hprefix tailTrace_3612099
  have hstable : (prefixWord ++ tailWord_3612099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612099).length < 2 ^ (prefixWord ++ tailWord_3612099).sum := by decide
  have hdescent : baseEnd_3612099 < baseStart_3612099 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612112 : List Nat := [2, 1, 1, 1, 1, 2, 2, 5, 3, 5]
def baseStart_3612112 : Nat := 118140960795 + 3612112 * 2 ^ 59
def prefixEnd_3612112 : Nat := 4983230072969 + 3 ^ 40 * 3612112 * 2
def baseEnd_3612112 : Nat := 618249877957758942962735

theorem tailTrace_3612112 : CollatzResearch.WordTrace tailWord_3612112 prefixEnd_3612112 618249877957758942962735 := by
  unfold tailWord_3612112
  simp only [CollatzResearch.WordTrace]
  refine ⟨65872273944971299230411295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87829698593295065640548393 65872273944971299230411295)
  ·
    refine ⟨98808410917456948845616943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65872273944971299230411295 98808410917456948845616943)
    ·
      refine ⟨148212616376185423268425415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98808410917456948845616943 148212616376185423268425415)
      ·
        refine ⟨222318924564278134902638123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148212616376185423268425415 222318924564278134902638123)
        ·
          refine ⟨333478386846417202353957185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222318924564278134902638123 333478386846417202353957185)
          ·
            refine ⟨250108790134812901765467889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 333478386846417202353957185 250108790134812901765467889)
            ·
              refine ⟨187581592601109676324100917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250108790134812901765467889 187581592601109676324100917)
              ·
                refine ⟨17585774306354032155384461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 187581592601109676324100917 17585774306354032155384461)
                ·
                  refine ⟨6594665364882762058269173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17585774306354032155384461 6594665364882762058269173)
                  ·
                    refine ⟨618249877957758942962735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6594665364882762058269173 618249877957758942962735)
                    ·
                      rfl

theorem cell23_3612112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 3, 5].length) (baseStart_3612112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3612112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3612112 prefixEnd_3612112 := by exact prefixLift 3612112
  have htrace : WordTrace (prefixWord ++ tailWord_3612112) baseStart_3612112 baseEnd_3612112 := by
    simpa [prefixWord, tailWord_3612112, baseEnd_3612112] using wordTrace_append hprefix tailTrace_3612112
  have hstable : (prefixWord ++ tailWord_3612112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612112).length < 2 ^ (prefixWord ++ tailWord_3612112).sum := by decide
  have hdescent : baseEnd_3612112 < baseStart_3612112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612119 : List Nat := [1, 1, 3, 2, 1, 1, 1, 5, 1, 5, 2]
def baseStart_3612119 : Nat := 118140960795 + 3612119 * 2 ^ 59
def prefixEnd_3612119 : Nat := 4983230072969 + 3 ^ 40 * 3612119 * 2
def baseEnd_3612119 : Nat := 1854753228237858301500673

theorem tailTrace_3612119 : CollatzResearch.WordTrace tailWord_3612119 prefixEnd_3612119 1854753228237858301500673 := by
  unfold tailWord_3612119
  simp only [CollatzResearch.WordTrace]
  refine ⟨131744803200917238656327411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87829868800611492437551607 131744803200917238656327411)
  ·
    refine ⟨197617204801375857984491117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131744803200917238656327411 197617204801375857984491117)
    ·
      refine ⟨74106451800515946744184169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197617204801375857984491117 74106451800515946744184169)
      ·
        refine ⟨55579838850386960058138127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74106451800515946744184169 55579838850386960058138127)
        ·
          refine ⟨83369758275580440087207191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55579838850386960058138127 83369758275580440087207191)
          ·
            refine ⟨125054637413370660130810787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83369758275580440087207191 125054637413370660130810787)
            ·
              refine ⟨187581956120055990196216181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125054637413370660130810787 187581956120055990196216181)
              ·
                refine ⟨17585808386255249080895267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 187581956120055990196216181 17585808386255249080895267)
                ·
                  refine ⟨26378712579382873621342901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17585808386255249080895267 26378712579382873621342901)
                  ·
                    refine ⟨2473004304317144402000897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26378712579382873621342901 2473004304317144402000897)
                    ·
                      refine ⟨1854753228237858301500673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2473004304317144402000897 1854753228237858301500673)
                      ·
                        rfl

theorem cell23_3612119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 5, 2].length) (baseStart_3612119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3612119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3612119 prefixEnd_3612119 := by exact prefixLift 3612119
  have htrace : WordTrace (prefixWord ++ tailWord_3612119) baseStart_3612119 baseEnd_3612119 := by
    simpa [prefixWord, tailWord_3612119, baseEnd_3612119] using wordTrace_append hprefix tailTrace_3612119
  have hstable : (prefixWord ++ tailWord_3612119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612119).length < 2 ^ (prefixWord ++ tailWord_3612119).sum := by decide
  have hdescent : baseEnd_3612119 < baseStart_3612119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612136 : List Nat := [2, 1, 4, 1, 1, 2, 1, 4, 2, 3, 2]
def baseStart_3612136 : Nat := 118140960795 + 3612136 * 2 ^ 59
def prefixEnd_3612136 : Nat := 4983230072969 + 3 ^ 40 * 3612136 * 2
def baseEnd_3612136 : Nat := 1854761957408984734988095

theorem tailTrace_3612136 : CollatzResearch.WordTrace tailWord_3612136 prefixEnd_3612136 1854761957408984734988095 := by
  unfold tailWord_3612136
  simp only [CollatzResearch.WordTrace]
  refine ⟨65872711620927825279848131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87830282161237100373130841 65872711620927825279848131)
  ·
    refine ⟨98809067431391737919772197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65872711620927825279848131 98809067431391737919772197)
    ·
      refine ⟨18526700143385950859957287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98809067431391737919772197 18526700143385950859957287)
      ·
        refine ⟨27790050215078926289935931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18526700143385950859957287 27790050215078926289935931)
        ·
          refine ⟨41685075322618389434903897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27790050215078926289935931 41685075322618389434903897)
          ·
            refine ⟨31263806491963792076177923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41685075322618389434903897 31263806491963792076177923)
            ·
              refine ⟨46895709737945688114266885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31263806491963792076177923 46895709737945688114266885)
              ·
                refine ⟨8792945575864816521425041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46895709737945688114266885 8792945575864816521425041)
                ·
                  refine ⟨6594709181898612391068781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8792945575864816521425041 6594709181898612391068781)
                  ·
                    refine ⟨2473015943211979646650793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6594709181898612391068781 2473015943211979646650793)
                    ·
                      refine ⟨1854761957408984734988095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2473015943211979646650793 1854761957408984734988095)
                      ·
                        rfl

theorem cell23_3612136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 4, 2, 3, 2].length) (baseStart_3612136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3612136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3612136 prefixEnd_3612136 := by exact prefixLift 3612136
  have htrace : WordTrace (prefixWord ++ tailWord_3612136) baseStart_3612136 baseEnd_3612136 := by
    simpa [prefixWord, tailWord_3612136, baseEnd_3612136] using wordTrace_append hprefix tailTrace_3612136
  have hstable : (prefixWord ++ tailWord_3612136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612136).length < 2 ^ (prefixWord ++ tailWord_3612136).sum := by decide
  have hdescent : baseEnd_3612136 < baseStart_3612136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612169 : List Nat := [1, 2, 1, 1, 3, 1, 3, 3, 3, 2, 3]
def baseStart_3612169 : Nat := 118140960795 + 3612169 * 2 ^ 59
def prefixEnd_3612169 : Nat := 4983230072969 + 3 ^ 40 * 3612169 * 2
def baseEnd_3612169 : Nat := 1854778902270583105875443

theorem tailTrace_3612169 : CollatzResearch.WordTrace tailWord_3612169 prefixEnd_3612169 1854778902270583105875443 := by
  unfold tailWord_3612169
  simp only [CollatzResearch.WordTrace]
  refine ⟨131746626850736097195647561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87831084567157398130431707 131746626850736097195647561)
  ·
    refine ⟨98809970138052072896735671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131746626850736097195647561 98809970138052072896735671)
    ·
      refine ⟨148214955207078109345103507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98809970138052072896735671 148214955207078109345103507)
      ·
        refine ⟨222322432810617164017655261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148214955207078109345103507 222322432810617164017655261)
        ·
          refine ⟨83370912303981436506620723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222322432810617164017655261 83370912303981436506620723)
          ·
            refine ⟨125056368455972154759931085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83370912303981436506620723 125056368455972154759931085)
            ·
              refine ⟨46896138170989558034974157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125056368455972154759931085 46896138170989558034974157)
              ·
                refine ⟨17586051814121084263115309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46896138170989558034974157 17586051814121084263115309)
                ·
                  refine ⟨6594769430295406598668241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17586051814121084263115309 6594769430295406598668241)
                  ·
                    refine ⟨4946077072721554949001181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6594769430295406598668241 4946077072721554949001181)
                    ·
                      refine ⟨1854778902270583105875443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4946077072721554949001181 1854778902270583105875443)
                      ·
                        rfl

theorem cell23_3612169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 3, 2, 3].length) (baseStart_3612169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3612169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3612169 prefixEnd_3612169 := by exact prefixLift 3612169
  have htrace : WordTrace (prefixWord ++ tailWord_3612169) baseStart_3612169 baseEnd_3612169 := by
    simpa [prefixWord, tailWord_3612169, baseEnd_3612169] using wordTrace_append hprefix tailTrace_3612169
  have hstable : (prefixWord ++ tailWord_3612169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612169).length < 2 ^ (prefixWord ++ tailWord_3612169).sum := by decide
  have hdescent : baseEnd_3612169 < baseStart_3612169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612179 : List Nat := [1, 1, 1, 2, 1, 6, 2, 2, 1, 2, 4]
def baseStart_3612179 : Nat := 118140960795 + 3612179 * 2 ^ 59
def prefixEnd_3612179 : Nat := 4983230072969 + 3 ^ 40 * 3612179 * 2
def baseEnd_3612179 : Nat := 1854784037077128066750397

theorem tailTrace_3612179 : CollatzResearch.WordTrace tailWord_3612179 prefixEnd_3612179 1854784037077128066750397 := by
  unfold tailWord_3612179
  simp only [CollatzResearch.WordTrace]
  refine ⟨131746991580699868903511591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87831327720466579269007727 131746991580699868903511591)
  ·
    refine ⟨197620487371049803355267387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131746991580699868903511591 197620487371049803355267387)
    ·
      refine ⟨296430731056574705032901081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197620487371049803355267387 296430731056574705032901081)
      ·
        refine ⟨222323048292431028774675811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296430731056574705032901081 222323048292431028774675811)
        ·
          refine ⟨333484572438646543162013717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222323048292431028774675811 333484572438646543162013717)
          ·
            refine ⟨15632089333061556710719393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 333484572438646543162013717 15632089333061556710719393)
            ·
              refine ⟨11724066999796167533039545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15632089333061556710719393 11724066999796167533039545)
              ·
                refine ⟨8793050249847125649779659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11724066999796167533039545 8793050249847125649779659)
                ·
                  refine ⟨13189575374770688474669489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8793050249847125649779659 13189575374770688474669489)
                  ·
                    refine ⟨9892181531078016356002117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13189575374770688474669489 9892181531078016356002117)
                    ·
                      refine ⟨1854784037077128066750397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9892181531078016356002117 1854784037077128066750397)
                      ·
                        rfl

theorem cell23_3612179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 2, 1, 2, 4].length) (baseStart_3612179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3612179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3612179 prefixEnd_3612179 := by exact prefixLift 3612179
  have htrace : WordTrace (prefixWord ++ tailWord_3612179) baseStart_3612179 baseEnd_3612179 := by
    simpa [prefixWord, tailWord_3612179, baseEnd_3612179] using wordTrace_append hprefix tailTrace_3612179
  have hstable : (prefixWord ++ tailWord_3612179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612179).length < 2 ^ (prefixWord ++ tailWord_3612179).sum := by decide
  have hdescent : baseEnd_3612179 < baseStart_3612179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612193 : List Nat := [1, 2, 3, 2, 2, 4, 1, 2, 2, 4]
def baseStart_3612193 : Nat := 118140960795 + 3612193 * 2 ^ 59
def prefixEnd_3612193 : Nat := 4983230072969 + 3 ^ 40 * 3612193 * 2
def baseEnd_3612193 : Nat := 618263741935430337325111

theorem tailTrace_3612193 : CollatzResearch.WordTrace tailWord_3612193 prefixEnd_3612193 618263741935430337325111 := by
  unfold tailWord_3612193
  simp only [CollatzResearch.WordTrace]
  refine ⟨131747502202649149294521233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87831668135099432863014155 131747502202649149294521233)
  ·
    refine ⟨98810626651986861970890925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131747502202649149294521233 98810626651986861970890925)
    ·
      refine ⟨37053984994495073239084097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98810626651986861970890925 37053984994495073239084097)
      ·
        refine ⟨27790488745871304929313073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37053984994495073239084097 27790488745871304929313073)
        ·
          refine ⟨20842866559403478696984805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27790488745871304929313073 20842866559403478696984805)
          ·
            refine ⟨3908037479888152255684651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20842866559403478696984805 3908037479888152255684651)
            ·
              refine ⟨5862056219832228383526977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3908037479888152255684651 5862056219832228383526977)
              ·
                refine ⟨4396542164874171287645233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5862056219832228383526977 4396542164874171287645233)
                ·
                  refine ⟨3297406623655628465733925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4396542164874171287645233 3297406623655628465733925)
                  ·
                    refine ⟨618263741935430337325111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3297406623655628465733925 618263741935430337325111)
                    ·
                      rfl

theorem cell23_3612193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 2, 2, 4].length) (baseStart_3612193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3612193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3612193 prefixEnd_3612193 := by exact prefixLift 3612193
  have htrace : WordTrace (prefixWord ++ tailWord_3612193) baseStart_3612193 baseEnd_3612193 := by
    simpa [prefixWord, tailWord_3612193, baseEnd_3612193] using wordTrace_append hprefix tailTrace_3612193
  have hstable : (prefixWord ++ tailWord_3612193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612193).length < 2 ^ (prefixWord ++ tailWord_3612193).sum := by decide
  have hdescent : baseEnd_3612193 < baseStart_3612193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612216 : List Nat := [2, 1, 2, 1, 4, 2, 3, 1, 1, 3, 3]
def baseStart_3612216 : Nat := 118140960795 + 3612216 * 2 ^ 59
def prefixEnd_3612216 : Nat := 4983230072969 + 3 ^ 40 * 3612216 * 2
def baseEnd_3612216 : Nat := 1854803035861344421987727

theorem tailTrace_3612216 : CollatzResearch.WordTrace tailWord_3612216 prefixEnd_3612216 1854803035861344421987727 := by
  unfold tailWord_3612216
  simp only [CollatzResearch.WordTrace]
  refine ⟨65874170540782912111304251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87832227387710549481739001 65874170540782912111304251)
  ·
    refine ⟨98811255811174368166956377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65874170540782912111304251 98811255811174368166956377)
    ·
      refine ⟨74108441858380776125217283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98811255811174368166956377 74108441858380776125217283)
      ·
        refine ⟨111162662787571164187825925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74108441858380776125217283 111162662787571164187825925)
        ·
          refine ⟨20842999272669593285217361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111162662787571164187825925 20842999272669593285217361)
          ·
            refine ⟨15632249454502194963913021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20842999272669593285217361 15632249454502194963913021)
            ·
              refine ⟨5862093545438323111467383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15632249454502194963913021 5862093545438323111467383)
              ·
                refine ⟨8793140318157484667201075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5862093545438323111467383 8793140318157484667201075)
                ·
                  refine ⟨13189710477236227000801613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8793140318157484667201075 13189710477236227000801613)
                  ·
                    refine ⟨4946141428963585125300605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13189710477236227000801613 4946141428963585125300605)
                    ·
                      refine ⟨1854803035861344421987727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4946141428963585125300605 1854803035861344421987727)
                      ·
                        rfl

theorem cell23_3612216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 1, 1, 3, 3].length) (baseStart_3612216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3612216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3612216 prefixEnd_3612216 := by exact prefixLift 3612216
  have htrace : WordTrace (prefixWord ++ tailWord_3612216) baseStart_3612216 baseEnd_3612216 := by
    simpa [prefixWord, tailWord_3612216, baseEnd_3612216] using wordTrace_append hprefix tailTrace_3612216
  have hstable : (prefixWord ++ tailWord_3612216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612216).length < 2 ^ (prefixWord ++ tailWord_3612216).sum := by decide
  have hdescent : baseEnd_3612216 < baseStart_3612216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612277 : List Nat := [1, 3, 4, 2, 1, 3, 1, 2, 1, 3, 2]
def baseStart_3612277 : Nat := 118140960795 + 3612277 * 2 ^ 59
def prefixEnd_3612277 : Nat := 4983230072969 + 3 ^ 40 * 3612277 * 2
def baseEnd_3612277 : Nat := 1854834358181268683324947

theorem tailTrace_3612277 : CollatzResearch.WordTrace tailWord_3612277 prefixEnd_3612277 1854834358181268683324947 := by
  unfold tailWord_3612277
  simp only [CollatzResearch.WordTrace]
  refine ⟨131750565934344831640579085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87833710622896554427052723 131750565934344831640579085)
  ·
    refine ⟨49406462225379311865217157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131750565934344831640579085 49406462225379311865217157)
    ·
      refine ⟨9263711667258620974728217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49406462225379311865217157 9263711667258620974728217)
      ·
        refine ⟨6947783750443965731046163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9263711667258620974728217 6947783750443965731046163)
        ·
          refine ⟨10421675625665948596569245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6947783750443965731046163 10421675625665948596569245)
          ·
            refine ⟨3908128359624730723713467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10421675625665948596569245 3908128359624730723713467)
            ·
              refine ⟨5862192539437096085570201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3908128359624730723713467 5862192539437096085570201)
              ·
                refine ⟨4396644404577822064177651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5862192539437096085570201 4396644404577822064177651)
                ·
                  refine ⟨6594966606866733096266477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4396644404577822064177651 6594966606866733096266477)
                  ·
                    refine ⟨2473112477575024911099929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6594966606866733096266477 2473112477575024911099929)
                    ·
                      refine ⟨1854834358181268683324947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2473112477575024911099929 1854834358181268683324947)
                      ·
                        rfl

theorem cell23_3612277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_3612277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3612277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3612277 prefixEnd_3612277 := by exact prefixLift 3612277
  have htrace : WordTrace (prefixWord ++ tailWord_3612277) baseStart_3612277 baseEnd_3612277 := by
    simpa [prefixWord, tailWord_3612277, baseEnd_3612277] using wordTrace_append hprefix tailTrace_3612277
  have hstable : (prefixWord ++ tailWord_3612277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612277).length < 2 ^ (prefixWord ++ tailWord_3612277).sum := by decide
  have hdescent : baseEnd_3612277 < baseStart_3612277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612333 : List Nat := [1, 5, 2, 1, 1, 1, 1, 2, 2, 5, 2]
def baseStart_3612333 : Nat := 118140960795 + 3612333 * 2 ^ 59
def prefixEnd_3612333 : Nat := 4983230072969 + 3 ^ 40 * 3612333 * 2
def baseEnd_3612333 : Nat := 1854863113097920464224689

theorem tailTrace_3612333 : CollatzResearch.WordTrace tailWord_3612333 prefixEnd_3612333 1854863113097920464224689 := by
  unfold tailWord_3612333
  simp only [CollatzResearch.WordTrace]
  refine ⟨131752608422141953204617653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87835072281427968803078435 131752608422141953204617653)
  ·
    refine ⟨12351807039575808112932905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 131752608422141953204617653 12351807039575808112932905)
    ·
      refine ⟨9263855279681856084699679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12351807039575808112932905 9263855279681856084699679)
      ·
        refine ⟨13895782919522784127049519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9263855279681856084699679 13895782919522784127049519)
        ·
          refine ⟨20843674379284176190574279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13895782919522784127049519 20843674379284176190574279)
          ·
            refine ⟨31265511568926264285861419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20843674379284176190574279 31265511568926264285861419)
            ·
              refine ⟨46898267353389396428792129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31265511568926264285861419 46898267353389396428792129)
              ·
                refine ⟨35173700515042047321594097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46898267353389396428792129 35173700515042047321594097)
                ·
                  refine ⟨26380275386281535491195573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35173700515042047321594097 26380275386281535491195573)
                  ·
                    refine ⟨2473150817463893952299585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26380275386281535491195573 2473150817463893952299585)
                    ·
                      refine ⟨1854863113097920464224689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2473150817463893952299585 1854863113097920464224689)
                      ·
                        rfl

theorem cell23_3612333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_3612333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3612333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3612333 prefixEnd_3612333 := by exact prefixLift 3612333
  have htrace : WordTrace (prefixWord ++ tailWord_3612333) baseStart_3612333 baseEnd_3612333 := by
    simpa [prefixWord, tailWord_3612333, baseEnd_3612333] using wordTrace_append hprefix tailTrace_3612333
  have hstable : (prefixWord ++ tailWord_3612333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612333).length < 2 ^ (prefixWord ++ tailWord_3612333).sum := by decide
  have hdescent : baseEnd_3612333 < baseStart_3612333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612343 : List Nat := [1, 1, 3, 1, 5, 3, 1, 1, 2, 5]
def baseStart_3612343 : Nat := 118140960795 + 3612343 * 2 ^ 59
def prefixEnd_3612343 : Nat := 4983230072969 + 3 ^ 40 * 3612343 * 2
def baseEnd_3612343 : Nat := 618289415968155141699881

theorem tailTrace_3612343 : CollatzResearch.WordTrace tailWord_3612343 prefixEnd_3612343 618289415968155141699881 := by
  unfold tailWord_3612343
  simp only [CollatzResearch.WordTrace]
  refine ⟨131752973152105724912481683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87835315434737149941654455 131752973152105724912481683)
  ·
    refine ⟨197629459728158587368722525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131752973152105724912481683 197629459728158587368722525)
    ·
      refine ⟨74111047398059470263270947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197629459728158587368722525 74111047398059470263270947)
      ·
        refine ⟨111166571097089205394906421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74111047398059470263270947 111166571097089205394906421)
        ·
          refine ⟨10421866040352113005772477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 111166571097089205394906421 10421866040352113005772477)
          ·
            refine ⟨3908199765132042377164679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10421866040352113005772477 3908199765132042377164679)
            ·
              refine ⟨5862299647698063565747019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3908199765132042377164679 5862299647698063565747019)
              ·
                refine ⟨8793449471547095348620529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5862299647698063565747019 8793449471547095348620529)
                ·
                  refine ⟨6595087103660321511465397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8793449471547095348620529 6595087103660321511465397)
                  ·
                    refine ⟨618289415968155141699881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6595087103660321511465397 618289415968155141699881)
                    ·
                      rfl

theorem cell23_3612343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 1, 2, 5].length) (baseStart_3612343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3612343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3612343 prefixEnd_3612343 := by exact prefixLift 3612343
  have htrace : WordTrace (prefixWord ++ tailWord_3612343) baseStart_3612343 baseEnd_3612343 := by
    simpa [prefixWord, tailWord_3612343, baseEnd_3612343] using wordTrace_append hprefix tailTrace_3612343
  have hstable : (prefixWord ++ tailWord_3612343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612343).length < 2 ^ (prefixWord ++ tailWord_3612343).sum := by decide
  have hdescent : baseEnd_3612343 < baseStart_3612343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612346 : List Nat := [3, 1, 1, 1, 2, 5, 1, 1, 1, 3, 4]
def baseStart_3612346 : Nat := 118140960795 + 3612346 * 2 ^ 59
def prefixEnd_3612346 : Nat := 4983230072969 + 3 ^ 40 * 3612346 * 2
def baseEnd_3612346 : Nat := 1854869788346428913362129

theorem tailTrace_3612346 : CollatzResearch.WordTrace tailWord_3612346 prefixEnd_3612346 1854869788346428913362129 := by
  unfold tailWord_3612346
  simp only [CollatzResearch.WordTrace]
  refine ⟨32938270642773714106210223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87835388380729904283227261 32938270642773714106210223)
  ·
    refine ⟨49407405964160571159315335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32938270642773714106210223 49407405964160571159315335)
    ·
      refine ⟨74111108946240856738973003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49407405964160571159315335 74111108946240856738973003)
      ·
        refine ⟨111166663419361285108459505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74111108946240856738973003 111166663419361285108459505)
        ·
          refine ⟨83374997564520963831344629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111166663419361285108459505 83374997564520963831344629)
          ·
            refine ⟨7816406021673840359188559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83374997564520963831344629 7816406021673840359188559)
            ·
              refine ⟨11724609032510760538782839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7816406021673840359188559 11724609032510760538782839)
              ·
                refine ⟨17586913548766140808174259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11724609032510760538782839 17586913548766140808174259)
                ·
                  refine ⟨26380370323149211212261389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17586913548766140808174259 26380370323149211212261389)
                  ·
                    refine ⟨9892638871180954204598021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26380370323149211212261389 9892638871180954204598021)
                    ·
                      refine ⟨1854869788346428913362129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9892638871180954204598021 1854869788346428913362129)
                      ·
                        rfl

theorem cell23_3612346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 1, 3, 4].length) (baseStart_3612346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3612346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3612346 prefixEnd_3612346 := by exact prefixLift 3612346
  have htrace : WordTrace (prefixWord ++ tailWord_3612346) baseStart_3612346 baseEnd_3612346 := by
    simpa [prefixWord, tailWord_3612346, baseEnd_3612346] using wordTrace_append hprefix tailTrace_3612346
  have hstable : (prefixWord ++ tailWord_3612346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612346).length < 2 ^ (prefixWord ++ tailWord_3612346).sum := by decide
  have hdescent : baseEnd_3612346 < baseStart_3612346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612359 : List Nat := [1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 6]
def baseStart_3612359 : Nat := 118140960795 + 3612359 * 2 ^ 59
def prefixEnd_3612359 : Nat := 4983230072969 + 3 ^ 40 * 3612359 * 2
def baseEnd_3612359 : Nat := 1854876463594937362499569

theorem tailTrace_3612359 : CollatzResearch.WordTrace tailWord_3612359 prefixEnd_3612359 1854876463594937362499569 := by
  unfold tailWord_3612359
  simp only [CollatzResearch.WordTrace]
  refine ⟨131753556720047759645064131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87835704480031839763376087 131753556720047759645064131)
  ·
    refine ⟨197630335080071639467596197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131753556720047759645064131 197630335080071639467596197)
    ·
      refine ⟨37055687827513432400174287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 197630335080071639467596197 37055687827513432400174287)
      ·
        refine ⟨55583531741270148600261431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37055687827513432400174287 55583531741270148600261431)
        ·
          refine ⟨83375297611905222900392147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55583531741270148600261431 83375297611905222900392147)
          ·
            refine ⟨125062946417857834350588221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83375297611905222900392147 125062946417857834350588221)
            ·
              refine ⟨46898604906696687881470583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125062946417857834350588221 46898604906696687881470583)
              ·
                refine ⟨70347907360045031822205875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46898604906696687881470583 70347907360045031822205875)
                ·
                  refine ⟨105521861040067547733308813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70347907360045031822205875 105521861040067547733308813)
                  ·
                    refine ⟨39570697890025330399990805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 105521861040067547733308813 39570697890025330399990805)
                    ·
                      refine ⟨1854876463594937362499569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39570697890025330399990805 1854876463594937362499569)
                      ·
                        rfl

theorem cell23_3612359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_3612359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3612359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3612359 prefixEnd_3612359 := by exact prefixLift 3612359
  have htrace : WordTrace (prefixWord ++ tailWord_3612359) baseStart_3612359 baseEnd_3612359 := by
    simpa [prefixWord, tailWord_3612359, baseEnd_3612359] using wordTrace_append hprefix tailTrace_3612359
  have hstable : (prefixWord ++ tailWord_3612359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612359).length < 2 ^ (prefixWord ++ tailWord_3612359).sum := by decide
  have hdescent : baseEnd_3612359 < baseStart_3612359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612430 : List Nat := [4, 1, 1, 2, 1, 1, 5, 1, 3, 1, 3]
def baseStart_3612430 : Nat := 118140960795 + 3612430 * 2 ^ 59
def prefixEnd_3612430 : Nat := 4983230072969 + 3 ^ 40 * 3612430 * 2
def baseEnd_3612430 : Nat := 1854912920721406584711743

theorem tailTrace_3612430 : CollatzResearch.WordTrace tailWord_3612430 prefixEnd_3612430 1854912920721406584711743 := by
  unfold tailWord_3612430
  simp only [CollatzResearch.WordTrace]
  refine ⟨16469518287848817346362343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87837430868527025847265829 16469518287848817346362343)
  ·
    refine ⟨24704277431773226019543515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16469518287848817346362343 24704277431773226019543515)
    ·
      refine ⟨37056416147659839029315273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24704277431773226019543515 37056416147659839029315273)
      ·
        refine ⟨27792312110744879271986455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37056416147659839029315273 27792312110744879271986455)
        ·
          refine ⟨41688468166117318907979683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27792312110744879271986455 41688468166117318907979683)
          ·
            refine ⟨62532702249175978361969525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41688468166117318907979683 62532702249175978361969525)
            ·
              refine ⟨5862440835860247971434643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62532702249175978361969525 5862440835860247971434643)
              ·
                refine ⟨8793661253790371957151965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5862440835860247971434643 8793661253790371957151965)
                ·
                  refine ⟨3297622970171389483931987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8793661253790371957151965 3297622970171389483931987)
                  ·
                    refine ⟨4946434455257084225897981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3297622970171389483931987 4946434455257084225897981)
                    ·
                      refine ⟨1854912920721406584711743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4946434455257084225897981 1854912920721406584711743)
                      ·
                        rfl

theorem cell23_3612430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 1, 3, 1, 3].length) (baseStart_3612430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3612430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3612430 prefixEnd_3612430 := by exact prefixLift 3612430
  have htrace : WordTrace (prefixWord ++ tailWord_3612430) baseStart_3612430 baseEnd_3612430 := by
    simpa [prefixWord, tailWord_3612430, baseEnd_3612430] using wordTrace_append hprefix tailTrace_3612430
  have hstable : (prefixWord ++ tailWord_3612430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612430).length < 2 ^ (prefixWord ++ tailWord_3612430).sum := by decide
  have hdescent : baseEnd_3612430 < baseStart_3612430 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612453 : List Nat := [1, 3, 1, 2, 3, 3, 1, 1, 3, 1, 4]
def baseStart_3612453 : Nat := 118140960795 + 3612453 * 2 ^ 59
def prefixEnd_3612453 : Nat := 4983230072969 + 3 ^ 40 * 3612453 * 2
def baseEnd_3612453 : Nat := 1854924730776459994724137

theorem tailTrace_3612453 : CollatzResearch.WordTrace tailWord_3612453 prefixEnd_3612453 1854924730776459994724137 := by
  unfold tailWord_3612453
  simp only [CollatzResearch.WordTrace]
  refine ⟨131756985181707213698986013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87837990121138142465990675 131756985181707213698986013)
  ·
    refine ⟨49408869443140205137119755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131756985181707213698986013 49408869443140205137119755)
    ·
      refine ⟨74113304164710307705679633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49408869443140205137119755 74113304164710307705679633)
      ·
        refine ⟨55584978123532730779259725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74113304164710307705679633 55584978123532730779259725)
        ·
          refine ⟨20844366796324774042222397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55584978123532730779259725 20844366796324774042222397)
          ·
            refine ⟨7816637548621790265833399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20844366796324774042222397 7816637548621790265833399)
            ·
              refine ⟨11724956322932685398750099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7816637548621790265833399 11724956322932685398750099)
              ·
                refine ⟨17587434484399028098125149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11724956322932685398750099 17587434484399028098125149)
                ·
                  refine ⟨6595287931649635536796931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17587434484399028098125149 6595287931649635536796931)
                  ·
                    refine ⟨9892931897474453305195397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6595287931649635536796931 9892931897474453305195397)
                    ·
                      refine ⟨1854924730776459994724137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9892931897474453305195397 1854924730776459994724137)
                      ·
                        rfl

theorem cell23_3612453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 3, 1, 4].length) (baseStart_3612453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3612453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3612453 prefixEnd_3612453 := by exact prefixLift 3612453
  have htrace : WordTrace (prefixWord ++ tailWord_3612453) baseStart_3612453 baseEnd_3612453 := by
    simpa [prefixWord, tailWord_3612453, baseEnd_3612453] using wordTrace_append hprefix tailTrace_3612453
  have hstable : (prefixWord ++ tailWord_3612453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612453).length < 2 ^ (prefixWord ++ tailWord_3612453).sum := by decide
  have hdescent : baseEnd_3612453 < baseStart_3612453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612500 : List Nat := [2, 4, 1, 1, 3, 2, 2, 1, 1, 2, 4]
def baseStart_3612500 : Nat := 118140960795 + 3612500 * 2 ^ 59
def prefixEnd_3612500 : Nat := 4983230072969 + 3 ^ 40 * 3612500 * 2
def baseEnd_3612500 : Nat := 1854948864367221310836421

theorem tailTrace_3612500 : CollatzResearch.WordTrace tailWord_3612500 prefixEnd_3612500 1854948864367221310836421 := by
  unfold tailWord_3612500
  simp only [CollatzResearch.WordTrace]
  refine ⟨65879349706268470362973477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87839132941691293817297969 65879349706268470362973477)
  ·
    refine ⟨12352378069925338193057527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65879349706268470362973477 12352378069925338193057527)
    ·
      refine ⟨18528567104888007289586291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12352378069925338193057527 18528567104888007289586291)
      ·
        refine ⟨27792850657332010934379437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18528567104888007289586291 27792850657332010934379437)
        ·
          refine ⟨10422318996499504100392289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27792850657332010934379437 10422318996499504100392289)
          ·
            refine ⟨7816739247374628075294217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10422318996499504100392289 7816739247374628075294217)
            ·
              refine ⟨5862554435530971056470663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7816739247374628075294217 5862554435530971056470663)
              ·
                refine ⟨8793831653296456584705995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5862554435530971056470663 8793831653296456584705995)
                ·
                  refine ⟨13190747479944684877058993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8793831653296456584705995 13190747479944684877058993)
                  ·
                    refine ⟨9893060609958513657794245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13190747479944684877058993 9893060609958513657794245)
                    ·
                      refine ⟨1854948864367221310836421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9893060609958513657794245 1854948864367221310836421)
                      ·
                        rfl

theorem cell23_3612500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_3612500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3612500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3612500 prefixEnd_3612500 := by exact prefixLift 3612500
  have htrace : WordTrace (prefixWord ++ tailWord_3612500) baseStart_3612500 baseEnd_3612500 := by
    simpa [prefixWord, tailWord_3612500, baseEnd_3612500] using wordTrace_append hprefix tailTrace_3612500
  have hstable : (prefixWord ++ tailWord_3612500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612500).length < 2 ^ (prefixWord ++ tailWord_3612500).sum := by decide
  have hdescent : baseEnd_3612500 < baseStart_3612500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612506 : List Nat := [3, 1, 1, 2, 1, 3, 1, 2, 2, 7]
def baseStart_3612506 : Nat := 118140960795 + 3612506 * 2 ^ 59
def prefixEnd_3612506 : Nat := 4983230072969 + 3 ^ 40 * 3612506 * 2
def baseEnd_3612506 : Nat := 618317315083716095787131

theorem tailTrace_3612506 : CollatzResearch.WordTrace tailWord_3612506 prefixEnd_3612506 618317315083716095787131 := by
  unfold tailWord_3612506
  simp only [CollatzResearch.WordTrace]
  refine ⟨32939729562628800937666343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87839278833676802500443581 32939729562628800937666343)
  ·
    refine ⟨49409594343943201406499515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32939729562628800937666343 49409594343943201406499515)
    ·
      refine ⟨74114391515914802109749273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49409594343943201406499515 74114391515914802109749273)
      ·
        refine ⟨55585793636936101582311955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74114391515914802109749273 55585793636936101582311955)
        ·
          refine ⟨83378690455404152373467933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55585793636936101582311955 83378690455404152373467933)
          ·
            refine ⟨31267008920776557140050475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83378690455404152373467933 31267008920776557140050475)
            ·
              refine ⟨46900513381164835710075713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31267008920776557140050475 46900513381164835710075713)
              ·
                refine ⟨35175385035873626782556785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46900513381164835710075713 35175385035873626782556785)
                ·
                  refine ⟨26381538776905220086917589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35175385035873626782556785 26381538776905220086917589)
                  ·
                    refine ⟨618317315083716095787131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26381538776905220086917589 618317315083716095787131)
                    ·
                      rfl

theorem cell23_3612506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 2, 7].length) (baseStart_3612506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3612506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3612506 prefixEnd_3612506 := by exact prefixLift 3612506
  have htrace : WordTrace (prefixWord ++ tailWord_3612506) baseStart_3612506 baseEnd_3612506 := by
    simpa [prefixWord, tailWord_3612506, baseEnd_3612506] using wordTrace_append hprefix tailTrace_3612506
  have hstable : (prefixWord ++ tailWord_3612506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612506).length < 2 ^ (prefixWord ++ tailWord_3612506).sum := by decide
  have hdescent : baseEnd_3612506 < baseStart_3612506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612520 : List Nat := [2, 1, 4, 2, 1, 1, 2, 2, 4, 1, 3]
def baseStart_3612520 : Nat := 118140960795 + 3612520 * 2 ^ 59
def prefixEnd_3612520 : Nat := 4983230072969 + 3 ^ 40 * 3612520 * 2
def baseEnd_3612520 : Nat := 1854959133980311232586329

theorem tailTrace_3612520 : CollatzResearch.WordTrace tailWord_3612520 prefixEnd_3612520 1854959133980311232586329 := by
  unfold tailWord_3612520
  simp only [CollatzResearch.WordTrace]
  refine ⟨65879714436232242070837507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87839619248309656094450009 65879714436232242070837507)
  ·
    refine ⟨98819571654348363106256261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65879714436232242070837507 98819571654348363106256261)
    ·
      refine ⟨18528669685190318082423049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98819571654348363106256261 18528669685190318082423049)
      ·
        refine ⟨13896502263892738561817287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18528669685190318082423049 13896502263892738561817287)
        ·
          refine ⟨20844753395839107842725931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13896502263892738561817287 20844753395839107842725931)
          ·
            refine ⟨31267130093758661764088897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20844753395839107842725931 31267130093758661764088897)
            ·
              refine ⟨23450347570318996323066673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31267130093758661764088897 23450347570318996323066673)
              ·
                refine ⟨17587760677739247242300005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23450347570318996323066673 17587760677739247242300005)
                ·
                  refine ⟨3297705127076108857931251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17587760677739247242300005 3297705127076108857931251)
                  ·
                    refine ⟨4946557690614163286896877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3297705127076108857931251 4946557690614163286896877)
                    ·
                      refine ⟨1854959133980311232586329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4946557690614163286896877 1854959133980311232586329)
                      ·
                        rfl

theorem cell23_3612520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_3612520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3612520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3612520 prefixEnd_3612520 := by exact prefixLift 3612520
  have htrace : WordTrace (prefixWord ++ tailWord_3612520) baseStart_3612520 baseEnd_3612520 := by
    simpa [prefixWord, tailWord_3612520, baseEnd_3612520] using wordTrace_append hprefix tailTrace_3612520
  have hstable : (prefixWord ++ tailWord_3612520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612520).length < 2 ^ (prefixWord ++ tailWord_3612520).sum := by decide
  have hdescent : baseEnd_3612520 < baseStart_3612520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612554 : List Nat := [3, 1, 2, 4, 3, 1, 1, 1, 1, 3, 3]
def baseStart_3612554 : Nat := 118140960795 + 3612554 * 2 ^ 59
def prefixEnd_3612554 : Nat := 4983230072969 + 3 ^ 40 * 3612554 * 2
def baseEnd_3612554 : Nat := 1854976592322564099561173

theorem tailTrace_3612554 : CollatzResearch.WordTrace tailWord_3612554 prefixEnd_3612554 1854976592322564099561173 := by
  unfold tailWord_3612554
  simp only [CollatzResearch.WordTrace]
  refine ⟨32940167238585326987103179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87840445969560871965608477 32940167238585326987103179)
  ·
    refine ⟨49410250857877990480654769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32940167238585326987103179 49410250857877990480654769)
    ·
      refine ⟨37057688143408492860491077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49410250857877990480654769 37057688143408492860491077)
      ·
        refine ⟨6948316526889092411342077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37057688143408492860491077 6948316526889092411342077)
        ·
          refine ⟨2605618697583409654253279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6948316526889092411342077 2605618697583409654253279)
          ·
            refine ⟨3908428046375114481379919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2605618697583409654253279 3908428046375114481379919)
            ·
              refine ⟨5862642069562671722069879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3908428046375114481379919 5862642069562671722069879)
              ·
                refine ⟨8793963104344007583104819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5862642069562671722069879 8793963104344007583104819)
                ·
                  refine ⟨13190944656516011374657229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8793963104344007583104819 13190944656516011374657229)
                  ·
                    refine ⟨4946604246193504265496461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13190944656516011374657229 4946604246193504265496461)
                    ·
                      refine ⟨1854976592322564099561173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4946604246193504265496461 1854976592322564099561173)
                      ·
                        rfl

theorem cell23_3612554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_3612554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3612554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3612554 prefixEnd_3612554 := by exact prefixLift 3612554
  have htrace : WordTrace (prefixWord ++ tailWord_3612554) baseStart_3612554 baseEnd_3612554 := by
    simpa [prefixWord, tailWord_3612554, baseEnd_3612554] using wordTrace_append hprefix tailTrace_3612554
  have hstable : (prefixWord ++ tailWord_3612554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612554).length < 2 ^ (prefixWord ++ tailWord_3612554).sum := by decide
  have hdescent : baseEnd_3612554 < baseStart_3612554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612560 : List Nat := [2, 1, 1, 1, 1, 1, 2, 4, 6, 2, 2]
def baseStart_3612560 : Nat := 118140960795 + 3612560 * 2 ^ 59
def prefixEnd_3612560 : Nat := 4983230072969 + 3 ^ 40 * 3612560 * 2
def baseEnd_3612560 : Nat := 1854979673206491076086145

theorem tailTrace_3612560 : CollatzResearch.WordTrace tailWord_3612560 prefixEnd_3612560 1854979673206491076086145 := by
  unfold tailWord_3612560
  simp only [CollatzResearch.WordTrace]
  refine ⟨65880443896159785486565567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87840591861546380648754089 65880443896159785486565567)
  ·
    refine ⟨98820665844239678229848351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65880443896159785486565567 98820665844239678229848351)
    ·
      refine ⟨148230998766359517344772527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98820665844239678229848351 148230998766359517344772527)
      ·
        refine ⟨222346498149539276017158791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148230998766359517344772527 222346498149539276017158791)
        ·
          refine ⟨333519747224308914025738187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222346498149539276017158791 333519747224308914025738187)
          ·
            refine ⟨500279620836463371038607281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333519747224308914025738187 500279620836463371038607281)
            ·
              refine ⟨375209715627347528278955461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 500279620836463371038607281 375209715627347528278955461)
              ·
                refine ⟨70351821680127661552304149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 375209715627347528278955461 70351821680127661552304149)
                ·
                  refine ⟨3297741641255984135264257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 70351821680127661552304149 3297741641255984135264257)
                  ·
                    refine ⟨2473306230941988101448193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3297741641255984135264257 2473306230941988101448193)
                    ·
                      refine ⟨1854979673206491076086145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2473306230941988101448193 1854979673206491076086145)
                      ·
                        rfl

theorem cell23_3612560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 6, 2, 2].length) (baseStart_3612560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3612560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3612560 prefixEnd_3612560 := by exact prefixLift 3612560
  have htrace : WordTrace (prefixWord ++ tailWord_3612560) baseStart_3612560 baseEnd_3612560 := by
    simpa [prefixWord, tailWord_3612560, baseEnd_3612560] using wordTrace_append hprefix tailTrace_3612560
  have hstable : (prefixWord ++ tailWord_3612560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612560).length < 2 ^ (prefixWord ++ tailWord_3612560).sum := by decide
  have hdescent : baseEnd_3612560 < baseStart_3612560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612564 : List Nat := [2, 4, 2, 1, 1, 3, 2, 2, 1, 3, 2]
def baseStart_3612564 : Nat := 118140960795 + 3612564 * 2 ^ 59
def prefixEnd_3612564 : Nat := 4983230072969 + 3 ^ 40 * 3612564 * 2
def baseEnd_3612564 : Nat := 1854981727129109060436127

theorem tailTrace_3612564 : CollatzResearch.WordTrace tailWord_3612564 prefixEnd_3612564 1854981727129109060436127 := by
  unfold tailWord_3612564
  simp only [CollatzResearch.WordTrace]
  refine ⟨65880516842152539828138373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87840689122870053104184497 65880516842152539828138373)
  ·
    refine ⟨12352596907903601217775945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65880516842152539828138373 12352596907903601217775945)
    ·
      refine ⟨9264447680927700913331959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12352596907903601217775945 9264447680927700913331959)
      ·
        refine ⟨13896671521391551369997939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9264447680927700913331959 13896671521391551369997939)
        ·
          refine ⟨20845007282087327054996909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13896671521391551369997939 20845007282087327054996909)
          ·
            refine ⟨7816877730782747645623841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20845007282087327054996909 7816877730782747645623841)
            ·
              refine ⟨5862658298087060734217881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7816877730782747645623841 5862658298087060734217881)
              ·
                refine ⟨4396993723565295550663411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5862658298087060734217881 4396993723565295550663411)
                ·
                  refine ⟨6595490585347943325995117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4396993723565295550663411 6595490585347943325995117)
                  ·
                    refine ⟨2473308969505478747248169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6595490585347943325995117 2473308969505478747248169)
                    ·
                      refine ⟨1854981727129109060436127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2473308969505478747248169 1854981727129109060436127)
                      ·
                        rfl

theorem cell23_3612564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_3612564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3612564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3612564 prefixEnd_3612564 := by exact prefixLift 3612564
  have htrace : WordTrace (prefixWord ++ tailWord_3612564) baseStart_3612564 baseEnd_3612564 := by
    simpa [prefixWord, tailWord_3612564, baseEnd_3612564] using wordTrace_append hprefix tailTrace_3612564
  have hstable : (prefixWord ++ tailWord_3612564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612564).length < 2 ^ (prefixWord ++ tailWord_3612564).sum := by decide
  have hdescent : baseEnd_3612564 < baseStart_3612564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612650 : List Nat := [3, 1, 3, 1, 2, 1, 1, 4, 2, 1, 4]
def baseStart_3612650 : Nat := 118140960795 + 3612650 * 2 ^ 59
def prefixEnd_3612650 : Nat := 4983230072969 + 3 ^ 40 * 3612650 * 2
def baseEnd_3612650 : Nat := 1855025886465395723960731

theorem tailTrace_3612650 : CollatzResearch.WordTrace tailWord_3612650 prefixEnd_3612650 1855025886465395723960731 := by
  unfold tailWord_3612650
  simp only [CollatzResearch.WordTrace]
  refine ⟨32941042590498379085976851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87842780241329010895938269 32941042590498379085976851)
  ·
    refine ⟨49411563885747568628965277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32941042590498379085976851 49411563885747568628965277)
    ·
      refine ⟨18529336457155338235861979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49411563885747568628965277 18529336457155338235861979)
      ·
        refine ⟨27794004685733007353792969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18529336457155338235861979 27794004685733007353792969)
        ·
          refine ⟨20845503514299755515344727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27794004685733007353792969 20845503514299755515344727)
          ·
            refine ⟨31268255271449633273017091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20845503514299755515344727 31268255271449633273017091)
            ·
              refine ⟨46902382907174449909525637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31268255271449633273017091 46902382907174449909525637)
              ·
                refine ⟨8794196795095209358036057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46902382907174449909525637 8794196795095209358036057)
                ·
                  refine ⟨6595647596321407018527043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8794196795095209358036057 6595647596321407018527043)
                  ·
                    refine ⟨9893471394482110527790565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6595647596321407018527043 9893471394482110527790565)
                    ·
                      refine ⟨1855025886465395723960731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9893471394482110527790565 1855025886465395723960731)
                      ·
                        rfl

theorem cell23_3612650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_3612650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3612650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3612650 prefixEnd_3612650 := by exact prefixLift 3612650
  have htrace : WordTrace (prefixWord ++ tailWord_3612650) baseStart_3612650 baseEnd_3612650 := by
    simpa [prefixWord, tailWord_3612650, baseEnd_3612650] using wordTrace_append hprefix tailTrace_3612650
  have hstable : (prefixWord ++ tailWord_3612650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612650).length < 2 ^ (prefixWord ++ tailWord_3612650).sum := by decide
  have hdescent : baseEnd_3612650 < baseStart_3612650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612737 : List Nat := [1, 2, 5, 1, 2, 1, 1, 4, 1, 5]
def baseStart_3612737 : Nat := 118140960795 + 3612737 * 2 ^ 59
def prefixEnd_3612737 : Nat := 4983230072969 + 3 ^ 40 * 3612737 * 2
def baseEnd_3612737 : Nat := 618356853094112294524277

theorem tailTrace_3612737 : CollatzResearch.WordTrace tailWord_3612737 prefixEnd_3612737 618356853094112294524277 := by
  unfold tailWord_3612737
  simp only [CollatzResearch.WordTrace]
  refine ⟨131767343512678330202324465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87844895675118886801549643 131767343512678330202324465)
  ·
    refine ⟨98825507634508747651743349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131767343512678330202324465 98825507634508747651743349)
    ·
      refine ⟨9264891340735195092350939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98825507634508747651743349 9264891340735195092350939)
      ·
        refine ⟨13897337011102792638526409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9264891340735195092350939 13897337011102792638526409)
        ·
          refine ⟨10423002758327094478894807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13897337011102792638526409 10423002758327094478894807)
          ·
            refine ⟨15634504137490641718342211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10423002758327094478894807 15634504137490641718342211)
            ·
              refine ⟨23451756206235962577513317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15634504137490641718342211 23451756206235962577513317)
              ·
                refine ⟨4397204288669242983283747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23451756206235962577513317 4397204288669242983283747)
                ·
                  refine ⟨6595806433003864474925621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4397204288669242983283747 6595806433003864474925621)
                  ·
                    refine ⟨618356853094112294524277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6595806433003864474925621 618356853094112294524277)
                    ·
                      rfl

theorem cell23_3612737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_3612737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3612737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3612737 prefixEnd_3612737 := by exact prefixLift 3612737
  have htrace : WordTrace (prefixWord ++ tailWord_3612737) baseStart_3612737 baseEnd_3612737 := by
    simpa [prefixWord, tailWord_3612737, baseEnd_3612737] using wordTrace_append hprefix tailTrace_3612737
  have hstable : (prefixWord ++ tailWord_3612737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612737).length < 2 ^ (prefixWord ++ tailWord_3612737).sum := by decide
  have hdescent : baseEnd_3612737 < baseStart_3612737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612757 : List Nat := [1, 3, 2, 2, 1, 3, 2, 3, 1, 1, 4]
def baseStart_3612757 : Nat := 118140960795 + 3612757 * 2 ^ 59
def prefixEnd_3612757 : Nat := 4983230072969 + 3 ^ 40 * 3612757 * 2
def baseEnd_3612757 : Nat := 1855080828895426805322739

theorem tailTrace_3612757 : CollatzResearch.WordTrace tailWord_3612757 prefixEnd_3612757 1855080828895426805322739 := by
  unfold tailWord_3612757
  simp only [CollatzResearch.WordTrace]
  refine ⟨131768072972605873618052525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87845381981737249078701683 131768072972605873618052525)
  ·
    refine ⟨49413027364727202606769697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131768072972605873618052525 49413027364727202606769697)
    ·
      refine ⟨37059770523545401955077273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49413027364727202606769697 37059770523545401955077273)
      ·
        refine ⟨27794827892659051466307955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37059770523545401955077273 27794827892659051466307955)
        ·
          refine ⟨41692241838988577199461933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27794827892659051466307955 41692241838988577199461933)
          ·
            refine ⟨15634590689620716449798225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41692241838988577199461933 15634590689620716449798225)
            ·
              refine ⟨11725943017215537337348669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15634590689620716449798225 11725943017215537337348669)
              ·
                refine ⟨4397228631455826501505751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11725943017215537337348669 4397228631455826501505751)
                ·
                  refine ⟨6595842947183739752258627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4397228631455826501505751 6595842947183739752258627)
                  ·
                    refine ⟨9893764420775609628387941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6595842947183739752258627 9893764420775609628387941)
                    ·
                      refine ⟨1855080828895426805322739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9893764420775609628387941 1855080828895426805322739)
                      ·
                        rfl

theorem cell23_3612757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 3, 1, 1, 4].length) (baseStart_3612757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3612757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3612757 prefixEnd_3612757 := by exact prefixLift 3612757
  have htrace : WordTrace (prefixWord ++ tailWord_3612757) baseStart_3612757 baseEnd_3612757 := by
    simpa [prefixWord, tailWord_3612757, baseEnd_3612757] using wordTrace_append hprefix tailTrace_3612757
  have hstable : (prefixWord ++ tailWord_3612757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612757).length < 2 ^ (prefixWord ++ tailWord_3612757).sum := by decide
  have hdescent : baseEnd_3612757 < baseStart_3612757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612760 : List Nat := [2, 1, 2, 2, 1, 4, 1, 3, 1, 1, 5]
def baseStart_3612760 : Nat := 118140960795 + 3612760 * 2 ^ 59
def prefixEnd_3612760 : Nat := 4983230072969 + 3 ^ 40 * 3612760 * 2
def baseEnd_3612760 : Nat := 1855082369337390293585225

theorem tailTrace_3612760 : CollatzResearch.WordTrace tailWord_3612760 prefixEnd_3612760 1855082369337390293585225 := by
  unfold tailWord_3612760
  simp only [CollatzResearch.WordTrace]
  refine ⟨65884091195797502565205867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87845454927730003420274489 65884091195797502565205867)
  ·
    refine ⟨98826136793696253847808801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65884091195797502565205867 98826136793696253847808801)
    ·
      refine ⟨74119602595272190385856601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98826136793696253847808801 74119602595272190385856601)
      ·
        refine ⟨55589701946454142789392451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74119602595272190385856601 55589701946454142789392451)
        ·
          refine ⟨83384552919681214184088677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55589701946454142789392451 83384552919681214184088677)
          ·
            refine ⟨15634603672440227659516627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83384552919681214184088677 15634603672440227659516627)
            ·
              refine ⟨23451905508660341489274941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15634603672440227659516627 23451905508660341489274941)
              ·
                refine ⟨8794464565747628058478103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23451905508660341489274941 8794464565747628058478103)
                ·
                  refine ⟨13191696848621442087717155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8794464565747628058478103 13191696848621442087717155)
                  ·
                    refine ⟨19787545272932163131575733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13191696848621442087717155 19787545272932163131575733)
                    ·
                      refine ⟨1855082369337390293585225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19787545272932163131575733 1855082369337390293585225)
                      ·
                        rfl

theorem cell23_3612760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 3, 1, 1, 5].length) (baseStart_3612760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3612760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3612760 prefixEnd_3612760 := by exact prefixLift 3612760
  have htrace : WordTrace (prefixWord ++ tailWord_3612760) baseStart_3612760 baseEnd_3612760 := by
    simpa [prefixWord, tailWord_3612760, baseEnd_3612760] using wordTrace_append hprefix tailTrace_3612760
  have hstable : (prefixWord ++ tailWord_3612760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612760).length < 2 ^ (prefixWord ++ tailWord_3612760).sum := by decide
  have hdescent : baseEnd_3612760 < baseStart_3612760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612780 : List Nat := [2, 2, 1, 1, 3, 4, 2, 8]
def baseStart_3612780 : Nat := 118140960795 + 3612780 * 2 ^ 59
def prefixEnd_3612780 : Nat := 4983230072969 + 3 ^ 40 * 3612780 * 2
def baseEnd_3612780 : Nat := 68707134775943711679079

theorem tailTrace_3612780 : CollatzResearch.WordTrace tailWord_3612780 prefixEnd_3612780 68707134775943711679079 := by
  unfold tailWord_3612780
  simp only [CollatzResearch.WordTrace]
  refine ⟨65884455925761274273069897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87845941234348365697426529 65884455925761274273069897)
  ·
    refine ⟨49413341944320955704802423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65884455925761274273069897 49413341944320955704802423)
    ·
      refine ⟨74120012916481433557203635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49413341944320955704802423 74120012916481433557203635)
      ·
        refine ⟨111180019374722150335805453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74120012916481433557203635 111180019374722150335805453)
        ·
          refine ⟨41692507265520806375927045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111180019374722150335805453 41692507265520806375927045)
          ·
            refine ⟨7817345112285151195486321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41692507265520806375927045 7817345112285151195486321)
            ·
              refine ⟨5863008834213863396614741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7817345112285151195486321 5863008834213863396614741)
              ·
                refine ⟨68707134775943711679079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5863008834213863396614741 68707134775943711679079)
                ·
                  rfl

theorem cell23_3612780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 8].length) (baseStart_3612780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3612780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3612780 prefixEnd_3612780 := by exact prefixLift 3612780
  have htrace : WordTrace (prefixWord ++ tailWord_3612780) baseStart_3612780 baseEnd_3612780 := by
    simpa [prefixWord, tailWord_3612780, baseEnd_3612780] using wordTrace_append hprefix tailTrace_3612780
  have hstable : (prefixWord ++ tailWord_3612780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612780).length < 2 ^ (prefixWord ++ tailWord_3612780).sum := by decide
  have hdescent : baseEnd_3612780 < baseStart_3612780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612784 : List Nat := [2, 1, 1, 1, 5, 2, 4, 1, 2, 4]
def baseStart_3612784 : Nat := 118140960795 + 3612784 * 2 ^ 59
def prefixEnd_3612784 : Nat := 4983230072969 + 3 ^ 40 * 3612784 * 2
def baseEnd_3612784 : Nat := 618364897624366066561705

theorem tailTrace_3612784 : CollatzResearch.WordTrace tailWord_3612784 prefixEnd_3612784 618364897624366066561705 := by
  unfold tailWord_3612784
  simp only [CollatzResearch.WordTrace]
  refine ⟨65884528871754028614642703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87846038495672038152856937 65884528871754028614642703)
  ·
    refine ⟨98826793307631042921964055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65884528871754028614642703 98826793307631042921964055)
    ·
      refine ⟨148240189961446564382946083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98826793307631042921964055 148240189961446564382946083)
      ·
        refine ⟨222360284942169846574419125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148240189961446564382946083 222360284942169846574419125)
        ·
          refine ⟨20846276713328423116351793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 222360284942169846574419125 20846276713328423116351793)
          ·
            refine ⟨15634707534996317337263845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20846276713328423116351793 15634707534996317337263845)
            ·
              refine ⟨2931507662811809500736971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15634707534996317337263845 2931507662811809500736971)
              ·
                refine ⟨4397261494217714251105457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2931507662811809500736971 4397261494217714251105457)
                ·
                  refine ⟨3297946120663285688329093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4397261494217714251105457 3297946120663285688329093)
                  ·
                    refine ⟨618364897624366066561705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3297946120663285688329093 618364897624366066561705)
                    ·
                      rfl

theorem cell23_3612784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4, 1, 2, 4].length) (baseStart_3612784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3612784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3612784 prefixEnd_3612784 := by exact prefixLift 3612784
  have htrace : WordTrace (prefixWord ++ tailWord_3612784) baseStart_3612784 baseEnd_3612784 := by
    simpa [prefixWord, tailWord_3612784, baseEnd_3612784] using wordTrace_append hprefix tailTrace_3612784
  have hstable : (prefixWord ++ tailWord_3612784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612784).length < 2 ^ (prefixWord ++ tailWord_3612784).sum := by decide
  have hdescent : baseEnd_3612784 < baseStart_3612784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612807 : List Nat := [1, 1, 4, 2, 1, 1, 2, 1, 6, 1, 3]
def baseStart_3612807 : Nat := 118140960795 + 3612807 * 2 ^ 59
def prefixEnd_3612807 : Nat := 4983230072969 + 3 ^ 40 * 3612807 * 2
def baseEnd_3612807 : Nat := 1855106502928151609697509

theorem tailTrace_3612807 : CollatzResearch.WordTrace tailWord_3612807 prefixEnd_3612807 1855106502928151609697509 := by
  unfold tailWord_3612807
  simp only [CollatzResearch.WordTrace]
  refine ⟨131769896622424732157372675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87846597748283154771581783 131769896622424732157372675)
  ·
    refine ⟨197654844933637098236059013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131769896622424732157372675 197654844933637098236059013)
    ·
      refine ⟨37060283425056955919261065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 197654844933637098236059013 37060283425056955919261065)
      ·
        refine ⟨27795212568792716939445799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37060283425056955919261065 27795212568792716939445799)
        ·
          refine ⟨41692818853189075409168699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27795212568792716939445799 41692818853189075409168699)
          ·
            refine ⟨62539228279783613113753049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41692818853189075409168699 62539228279783613113753049)
            ·
              refine ⟨46904421209837709835314787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62539228279783613113753049 46904421209837709835314787)
              ·
                refine ⟨70356631814756564752972181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46904421209837709835314787 70356631814756564752972181)
                ·
                  refine ⟨3297967116316713972795571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 70356631814756564752972181 3297967116316713972795571)
                  ·
                    refine ⟨4946950674475070959193357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3297967116316713972795571 4946950674475070959193357)
                    ·
                      refine ⟨1855106502928151609697509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4946950674475070959193357 1855106502928151609697509)
                      ·
                        rfl

theorem cell23_3612807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 6, 1, 3].length) (baseStart_3612807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3612807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3612807 prefixEnd_3612807 := by exact prefixLift 3612807
  have htrace : WordTrace (prefixWord ++ tailWord_3612807) baseStart_3612807 baseEnd_3612807 := by
    simpa [prefixWord, tailWord_3612807, baseEnd_3612807] using wordTrace_append hprefix tailTrace_3612807
  have hstable : (prefixWord ++ tailWord_3612807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612807).length < 2 ^ (prefixWord ++ tailWord_3612807).sum := by decide
  have hdescent : baseEnd_3612807 < baseStart_3612807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612864 : List Nat := [2, 1, 1, 2, 5, 1, 2, 2, 1, 4, 2]
def baseStart_3612864 : Nat := 118140960795 + 3612864 * 2 ^ 59
def prefixEnd_3612864 : Nat := 4983230072969 + 3 ^ 40 * 3612864 * 2
def baseEnd_3612864 : Nat := 1855135771325457886684747

theorem tailTrace_3612864 : CollatzResearch.WordTrace tailWord_3612864 prefixEnd_3612864 1855135771325457886684747 := by
  unfold tailWord_3612864
  simp only [CollatzResearch.WordTrace]
  refine ⟨65885987791609115446098823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87847983722145487261465097 65885987791609115446098823)
  ·
    refine ⟨98828981687413673169148235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65885987791609115446098823 98828981687413673169148235)
    ·
      refine ⟨148243472531120509753722353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98828981687413673169148235 148243472531120509753722353)
      ·
        refine ⟨111182604398340382315291765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148243472531120509753722353 111182604398340382315291765)
        ·
          refine ⟨10423369162344410842058603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 111182604398340382315291765 10423369162344410842058603)
          ·
            refine ⟨15635053743516616263087905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10423369162344410842058603 15635053743516616263087905)
            ·
              refine ⟨11726290307637462197315929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15635053743516616263087905 11726290307637462197315929)
              ·
                refine ⟨8794717730728096647986947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11726290307637462197315929 8794717730728096647986947)
                ·
                  refine ⟨13192076596092144971980421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8794717730728096647986947 13192076596092144971980421)
                  ·
                    refine ⟨2473514361767277182246329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13192076596092144971980421 2473514361767277182246329)
                    ·
                      refine ⟨1855135771325457886684747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2473514361767277182246329 1855135771325457886684747)
                      ·
                        rfl

theorem cell23_3612864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 2, 1, 4, 2].length) (baseStart_3612864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3612864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3612864 prefixEnd_3612864 := by exact prefixLift 3612864
  have htrace : WordTrace (prefixWord ++ tailWord_3612864) baseStart_3612864 baseEnd_3612864 := by
    simpa [prefixWord, tailWord_3612864, baseEnd_3612864] using wordTrace_append hprefix tailTrace_3612864
  have hstable : (prefixWord ++ tailWord_3612864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612864).length < 2 ^ (prefixWord ++ tailWord_3612864).sum := by decide
  have hdescent : baseEnd_3612864 < baseStart_3612864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612868 : List Nat := [2, 3, 3, 1, 2, 1, 4, 1, 1, 3, 2]
def baseStart_3612868 : Nat := 118140960795 + 3612868 * 2 ^ 59
def prefixEnd_3612868 : Nat := 4983230072969 + 3 ^ 40 * 3612868 * 2
def baseEnd_3612868 : Nat := 1855137825248075871034729

theorem tailTrace_3612868 : CollatzResearch.WordTrace tailWord_3612868 prefixEnd_3612868 1855137825248075871034729 := by
  unfold tailWord_3612868
  simp only [CollatzResearch.WordTrace]
  refine ⟨65886060737601869787671629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87848080983469159716895505 65886060737601869787671629)
  ·
    refine ⟨24707272776600701170376861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65886060737601869787671629 24707272776600701170376861)
    ·
      refine ⟨9265227291225262938891323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24707272776600701170376861 9265227291225262938891323)
      ·
        refine ⟨13897840936837894408336985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9265227291225262938891323 13897840936837894408336985)
        ·
          refine ⟨10423380702628420806252739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13897840936837894408336985 10423380702628420806252739)
          ·
            refine ⟨15635071053942631209379109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10423380702628420806252739 15635071053942631209379109)
            ·
              refine ⟨2931575822614243351758583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15635071053942631209379109 2931575822614243351758583)
              ·
                refine ⟨4397363733921365027637875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2931575822614243351758583 4397363733921365027637875)
                ·
                  refine ⟨6596045600882047541456813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4397363733921365027637875 6596045600882047541456813)
                  ·
                    refine ⟨2473517100330767828046305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6596045600882047541456813 2473517100330767828046305)
                    ·
                      refine ⟨1855137825248075871034729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2473517100330767828046305 1855137825248075871034729)
                      ·
                        rfl

theorem cell23_3612868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_3612868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3612868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3612868 prefixEnd_3612868 := by exact prefixLift 3612868
  have htrace : WordTrace (prefixWord ++ tailWord_3612868) baseStart_3612868 baseEnd_3612868 := by
    simpa [prefixWord, tailWord_3612868, baseEnd_3612868] using wordTrace_append hprefix tailTrace_3612868
  have hstable : (prefixWord ++ tailWord_3612868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612868).length < 2 ^ (prefixWord ++ tailWord_3612868).sum := by decide
  have hdescent : baseEnd_3612868 < baseStart_3612868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612881 : List Nat := [1, 2, 2, 1, 2, 2, 5, 2, 2, 2, 2]
def baseStart_3612881 : Nat := 118140960795 + 3612881 * 2 ^ 59
def prefixEnd_3612881 : Nat := 4983230072969 + 3 ^ 40 * 3612881 * 2
def baseEnd_3612881 : Nat := 1855144500496584320172169

theorem tailTrace_3612881 : CollatzResearch.WordTrace tailWord_3612881 prefixEnd_3612881 1855144500496584320172169 := by
  unfold tailWord_3612881
  simp only [CollatzResearch.WordTrace]
  refine ⟨131772595624156642795566497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87848397082771095197044331 131772595624156642795566497)
  ·
    refine ⟨98829446718117482096674873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131772595624156642795566497 98829446718117482096674873)
    ·
      refine ⟨74122085038588111572506155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98829446718117482096674873 74122085038588111572506155)
      ·
        refine ⟨111183127557882167358759233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74122085038588111572506155 111183127557882167358759233)
        ·
          refine ⟨83387345668411625519069425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111183127557882167358759233 83387345668411625519069425)
          ·
            refine ⟨62540509251308719139302069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83387345668411625519069425 62540509251308719139302069)
            ·
              refine ⟨5863172742310192419309569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62540509251308719139302069 5863172742310192419309569)
              ·
                refine ⟨4397379556732644314482177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5863172742310192419309569 4397379556732644314482177)
                ·
                  refine ⟨3298034667549483235861633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4397379556732644314482177 3298034667549483235861633)
                  ·
                    refine ⟨2473526000662112426896225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3298034667549483235861633 2473526000662112426896225)
                    ·
                      refine ⟨1855144500496584320172169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2473526000662112426896225 1855144500496584320172169)
                      ·
                        rfl

theorem cell23_3612881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 2, 2, 2, 2].length) (baseStart_3612881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3612881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3612881 prefixEnd_3612881 := by exact prefixLift 3612881
  have htrace : WordTrace (prefixWord ++ tailWord_3612881) baseStart_3612881 baseEnd_3612881 := by
    simpa [prefixWord, tailWord_3612881, baseEnd_3612881] using wordTrace_append hprefix tailTrace_3612881
  have hstable : (prefixWord ++ tailWord_3612881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612881).length < 2 ^ (prefixWord ++ tailWord_3612881).sum := by decide
  have hdescent : baseEnd_3612881 < baseStart_3612881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612897 : List Nat := [1, 2, 3, 1, 3, 1, 1, 3, 2, 3, 3]
def baseStart_3612897 : Nat := 118140960795 + 3612897 * 2 ^ 59
def prefixEnd_3612897 : Nat := 4983230072969 + 3 ^ 40 * 3612897 * 2
def baseEnd_3612897 : Nat := 1855152716187056257572095

theorem tailTrace_3612897 : CollatzResearch.WordTrace tailWord_3612897 prefixEnd_3612897 1855152716187056257572095 := by
  unfold tailWord_3612897
  simp only [CollatzResearch.WordTrace]
  refine ⟨131773179192098677528148945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87848786128065785018765963 131773179192098677528148945)
  ·
    refine ⟨98829884394074008146111709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131773179192098677528148945 98829884394074008146111709)
    ·
      refine ⟨37061206647777753054791891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98829884394074008146111709 37061206647777753054791891)
      ·
        refine ⟨55591809971666629582187837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37061206647777753054791891 55591809971666629582187837)
        ·
          refine ⟨20846928739374986093320439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55591809971666629582187837 20846928739374986093320439)
          ·
            refine ⟨31270393109062479139980659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20846928739374986093320439 31270393109062479139980659)
            ·
              refine ⟨46905589663593718709970989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31270393109062479139980659 46905589663593718709970989)
              ·
                refine ⟨17589596123847644516239121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46905589663593718709970989 17589596123847644516239121)
                ·
                  refine ⟨13192197092885733387179341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17589596123847644516239121 13192197092885733387179341)
                  ·
                    refine ⟨4947073909832150020192253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13192197092885733387179341 4947073909832150020192253)
                    ·
                      refine ⟨1855152716187056257572095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4947073909832150020192253 1855152716187056257572095)
                      ·
                        rfl

theorem cell23_3612897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 2, 3, 3].length) (baseStart_3612897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3612897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3612897 prefixEnd_3612897 := by exact prefixLift 3612897
  have htrace : WordTrace (prefixWord ++ tailWord_3612897) baseStart_3612897 baseEnd_3612897 := by
    simpa [prefixWord, tailWord_3612897, baseEnd_3612897] using wordTrace_append hprefix tailTrace_3612897
  have hstable : (prefixWord ++ tailWord_3612897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612897).length < 2 ^ (prefixWord ++ tailWord_3612897).sum := by decide
  have hdescent : baseEnd_3612897 < baseStart_3612897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612937 : List Nat := [1, 2, 1, 1, 3, 4, 1, 1, 4, 1, 4]
def baseStart_3612937 : Nat := 118140960795 + 3612937 * 2 ^ 59
def prefixEnd_3612937 : Nat := 4983230072969 + 3 ^ 40 * 3612937 * 2
def baseEnd_3612937 : Nat := 1855173255413236101071911

theorem tailTrace_3612937 : CollatzResearch.WordTrace tailWord_3612937 prefixEnd_3612937 1855173255413236101071911 := by
  unfold tailWord_3612937
  simp only [CollatzResearch.WordTrace]
  refine ⟨131774638111953764359605065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87849758741302509573070043 131774638111953764359605065)
  ·
    refine ⟨98830978583965323269703799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131774638111953764359605065 98830978583965323269703799)
    ·
      refine ⟨148246467875947984904555699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98830978583965323269703799 148246467875947984904555699)
      ·
        refine ⟨222369701813921977356833549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148246467875947984904555699 222369701813921977356833549)
        ·
          refine ⟨83388638180220741508812581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222369701813921977356833549 83388638180220741508812581)
          ·
            refine ⟨15635369658791389032902359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83388638180220741508812581 15635369658791389032902359)
            ·
              refine ⟨23453054488187083549353539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15635369658791389032902359 23453054488187083549353539)
              ·
                refine ⟨35179581732280625324030309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23453054488187083549353539 35179581732280625324030309)
                ·
                  refine ⟨6596171574802617248255683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35179581732280625324030309 6596171574802617248255683)
                  ·
                    refine ⟨9894257362203925872383525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6596171574802617248255683 9894257362203925872383525)
                    ·
                      refine ⟨1855173255413236101071911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9894257362203925872383525 1855173255413236101071911)
                      ·
                        rfl

theorem cell23_3612937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 4, 1, 4].length) (baseStart_3612937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3612937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3612937 prefixEnd_3612937 := by exact prefixLift 3612937
  have htrace : WordTrace (prefixWord ++ tailWord_3612937) baseStart_3612937 baseEnd_3612937 := by
    simpa [prefixWord, tailWord_3612937, baseEnd_3612937] using wordTrace_append hprefix tailTrace_3612937
  have hstable : (prefixWord ++ tailWord_3612937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612937).length < 2 ^ (prefixWord ++ tailWord_3612937).sum := by decide
  have hdescent : baseEnd_3612937 < baseStart_3612937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3612981 : List Nat := [1, 3, 3, 1, 2, 1, 2, 5, 1, 4]
def baseStart_3612981 : Nat := 118140960795 + 3612981 * 2 ^ 59
def prefixEnd_3612981 : Nat := 4983230072969 + 3 ^ 40 * 3612981 * 2
def baseEnd_3612981 : Nat := 618398616187344642973903

theorem tailTrace_3612981 : CollatzResearch.WordTrace tailWord_3612981 prefixEnd_3612981 618398616187344642973903 := by
  unfold tailWord_3612981
  simp only [CollatzResearch.WordTrace]
  refine ⟨131776242923794359874206797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87850828615862906582804531 131776242923794359874206797)
  ·
    refine ⟨49416091096422884952827549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131776242923794359874206797 49416091096422884952827549)
    ·
      refine ⟨18531034161158581857310331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49416091096422884952827549 18531034161158581857310331)
      ·
        refine ⟨27796551241737872785965497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18531034161158581857310331 27796551241737872785965497)
        ·
          refine ⟨20847413431303404589474123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27796551241737872785965497 20847413431303404589474123)
          ·
            refine ⟨31271120146955106884211185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20847413431303404589474123 31271120146955106884211185)
            ·
              refine ⟨23453340110216330163158389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31271120146955106884211185 23453340110216330163158389)
              ·
                refine ⟨2198750635332780952796099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23453340110216330163158389 2198750635332780952796099)
                ·
                  refine ⟨3298125952999171429194149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2198750635332780952796099 3298125952999171429194149)
                  ·
                    refine ⟨618398616187344642973903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3298125952999171429194149 618398616187344642973903)
                    ·
                      rfl

theorem cell23_3612981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 5, 1, 4].length) (baseStart_3612981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3612981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3612981 prefixEnd_3612981 := by exact prefixLift 3612981
  have htrace : WordTrace (prefixWord ++ tailWord_3612981) baseStart_3612981 baseEnd_3612981 := by
    simpa [prefixWord, tailWord_3612981, baseEnd_3612981] using wordTrace_append hprefix tailTrace_3612981
  have hstable : (prefixWord ++ tailWord_3612981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3612981).length < 2 ^ (prefixWord ++ tailWord_3612981).sum := by decide
  have hdescent : baseEnd_3612981 < baseStart_3612981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3612981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613031 : List Nat := [1, 1, 5, 1, 3, 2, 1, 1, 1, 5, 2]
def baseStart_3613031 : Nat := 118140960795 + 3613031 * 2 ^ 59
def prefixEnd_3613031 : Nat := 4983230072969 + 3 ^ 40 * 3613031 * 2
def baseEnd_3613031 : Nat := 1855221522594758733296479

theorem tailTrace_3613031 : CollatzResearch.WordTrace tailWord_3613031 prefixEnd_3613031 1855221522594758733296479 := by
  unfold tailWord_3613031
  simp only [CollatzResearch.WordTrace]
  refine ⟨131778066573613218413526947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87852044382408812275684631 131778066573613218413526947)
  ·
    refine ⟨197667099860419827620290421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131778066573613218413526947 197667099860419827620290421)
    ·
      refine ⟨18531290611914358839402227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 197667099860419827620290421 18531290611914358839402227)
      ·
        refine ⟨27796935917871538259103341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18531290611914358839402227 27796935917871538259103341)
        ·
          refine ⟨10423850969201826847163753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27796935917871538259103341 10423850969201826847163753)
          ·
            refine ⟨7817888226901370135372815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10423850969201826847163753 7817888226901370135372815)
            ·
              refine ⟨11726832340352055203059223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7817888226901370135372815 11726832340352055203059223)
              ·
                refine ⟨17590248510528082804588835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11726832340352055203059223 17590248510528082804588835)
                ·
                  refine ⟨26385372765792124206883253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17590248510528082804588835 26385372765792124206883253)
                  ·
                    refine ⟨2473628696793011644395305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26385372765792124206883253 2473628696793011644395305)
                    ·
                      refine ⟨1855221522594758733296479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2473628696793011644395305 1855221522594758733296479)
                      ·
                        rfl

theorem cell23_3613031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 5, 2].length) (baseStart_3613031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3613031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3613031 prefixEnd_3613031 := by exact prefixLift 3613031
  have htrace : WordTrace (prefixWord ++ tailWord_3613031) baseStart_3613031 baseEnd_3613031 := by
    simpa [prefixWord, tailWord_3613031, baseEnd_3613031] using wordTrace_append hprefix tailTrace_3613031
  have hstable : (prefixWord ++ tailWord_3613031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613031).length < 2 ^ (prefixWord ++ tailWord_3613031).sum := by decide
  have hdescent : baseEnd_3613031 < baseStart_3613031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613064 : List Nat := [2, 1, 3, 3, 1, 1, 3, 2, 1, 1, 5]
def baseStart_3613064 : Nat := 118140960795 + 3613064 * 2 ^ 59
def prefixEnd_3613064 : Nat := 4983230072969 + 3 ^ 40 * 3613064 * 2
def baseEnd_3613064 : Nat := 1855238467456357104183827

theorem tailTrace_3613064 : CollatzResearch.WordTrace tailWord_3613064 prefixEnd_3613064 1855238467456357104183827 := by
  unfold tailWord_3613064
  simp only [CollatzResearch.WordTrace]
  refine ⟨65889635091246832524739123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87852846788329110032985497 65889635091246832524739123)
  ·
    refine ⟨98834452636870248787108685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65889635091246832524739123 98834452636870248787108685)
    ·
      refine ⟨37062919738826343295165757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98834452636870248787108685 37062919738826343295165757)
      ·
        refine ⟨13898594902059878735687159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37062919738826343295165757 13898594902059878735687159)
        ·
          refine ⟨20847892353089818103530739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13898594902059878735687159 20847892353089818103530739)
          ·
            refine ⟨31271838529634727155296109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20847892353089818103530739 31271838529634727155296109)
            ·
              refine ⟨11726939448613022683236041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31271838529634727155296109 11726939448613022683236041)
              ·
                refine ⟨8795204586459767012427031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11726939448613022683236041 8795204586459767012427031)
                ·
                  refine ⟨13192806879689650518640547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8795204586459767012427031 13192806879689650518640547)
                  ·
                    refine ⟨19789210319534475777960821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13192806879689650518640547 19789210319534475777960821)
                    ·
                      refine ⟨1855238467456357104183827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19789210319534475777960821 1855238467456357104183827)
                      ·
                        rfl

theorem cell23_3613064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_3613064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3613064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3613064 prefixEnd_3613064 := by exact prefixLift 3613064
  have htrace : WordTrace (prefixWord ++ tailWord_3613064) baseStart_3613064 baseEnd_3613064 := by
    simpa [prefixWord, tailWord_3613064, baseEnd_3613064] using wordTrace_append hprefix tailTrace_3613064
  have hstable : (prefixWord ++ tailWord_3613064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613064).length < 2 ^ (prefixWord ++ tailWord_3613064).sum := by decide
  have hdescent : baseEnd_3613064 < baseStart_3613064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613081 : List Nat := [1, 2, 1, 2, 1, 4, 4, 2, 1, 2, 3]
def baseStart_3613081 : Nat := 118140960795 + 3613081 * 2 ^ 59
def prefixEnd_3613081 : Nat := 4983230072969 + 3 ^ 40 * 3613081 * 2
def baseEnd_3613081 : Nat := 1855247196627483537671249

theorem tailTrace_3613081 : CollatzResearch.WordTrace tailWord_3613081 prefixEnd_3613081 1855247196627483537671249 := by
  unfold tailWord_3613081
  simp only [CollatzResearch.WordTrace]
  refine ⟨131779890223432076952847097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87853260148954717968564731 131779890223432076952847097)
  ·
    refine ⟨98834917667574057714635323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131779890223432076952847097 98834917667574057714635323)
    ·
      refine ⟨148252376501361086571952985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98834917667574057714635323 148252376501361086571952985)
      ·
        refine ⟨111189282376020814928964739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148252376501361086571952985 111189282376020814928964739)
        ·
          refine ⟨166783923564031222393447109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111189282376020814928964739 166783923564031222393447109)
          ·
            refine ⟨31271985668255854198771333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 166783923564031222393447109 31271985668255854198771333)
            ·
              refine ⟨5863497312797972662269625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31271985668255854198771333 5863497312797972662269625)
              ·
                refine ⟨4397622984598479496702219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5863497312797972662269625 4397622984598479496702219)
                ·
                  refine ⟨6596434476897719245053329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4397622984598479496702219 6596434476897719245053329)
                  ·
                    refine ⟨4947325857673289433789997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6596434476897719245053329 4947325857673289433789997)
                    ·
                      refine ⟨1855247196627483537671249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4947325857673289433789997 1855247196627483537671249)
                      ·
                        rfl

theorem cell23_3613081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 2, 1, 2, 3].length) (baseStart_3613081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3613081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3613081 prefixEnd_3613081 := by exact prefixLift 3613081
  have htrace : WordTrace (prefixWord ++ tailWord_3613081) baseStart_3613081 baseEnd_3613081 := by
    simpa [prefixWord, tailWord_3613081, baseEnd_3613081] using wordTrace_append hprefix tailTrace_3613081
  have hstable : (prefixWord ++ tailWord_3613081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613081).length < 2 ^ (prefixWord ++ tailWord_3613081).sum := by decide
  have hdescent : baseEnd_3613081 < baseStart_3613081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613089 : List Nat := [1, 2, 3, 5, 2, 1, 1, 3, 1, 1, 3]
def baseStart_3613089 : Nat := 118140960795 + 3613089 * 2 ^ 59
def prefixEnd_3613089 : Nat := 4983230072969 + 3 ^ 40 * 3613089 * 2
def baseEnd_3613089 : Nat := 1855251304472719506371213

theorem tailTrace_3613089 : CollatzResearch.WordTrace tailWord_3613089 prefixEnd_3613089 1855251304472719506371213 := by
  unfold tailWord_3613089
  simp only [CollatzResearch.WordTrace]
  refine ⟨131780182007403094319138321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87853454671602062879425547 131780182007403094319138321)
  ·
    refine ⟨98835136505552320739353741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131780182007403094319138321 98835136505552320739353741)
    ·
      refine ⟨37063176189582120277257653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98835136505552320739353741 37063176189582120277257653)
      ·
        refine ⟨3474672767773323775992905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37063176189582120277257653 3474672767773323775992905)
        ·
          refine ⟨2606004575829992831994679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3474672767773323775992905 2606004575829992831994679)
          ·
            refine ⟨3909006863744989247992019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2606004575829992831994679 3909006863744989247992019)
            ·
              refine ⟨5863510295617483871988029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3909006863744989247992019 5863510295617483871988029)
              ·
                refine ⟨2198816360856556451995511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5863510295617483871988029 2198816360856556451995511)
                ·
                  refine ⟨3298224541284834677993267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2198816360856556451995511 3298224541284834677993267)
                  ·
                    refine ⟨4947336811927252016989901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3298224541284834677993267 4947336811927252016989901)
                    ·
                      refine ⟨1855251304472719506371213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4947336811927252016989901 1855251304472719506371213)
                      ·
                        rfl

theorem cell23_3613089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_3613089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3613089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3613089 prefixEnd_3613089 := by exact prefixLift 3613089
  have htrace : WordTrace (prefixWord ++ tailWord_3613089) baseStart_3613089 baseEnd_3613089 := by
    simpa [prefixWord, tailWord_3613089, baseEnd_3613089] using wordTrace_append hprefix tailTrace_3613089
  have hstable : (prefixWord ++ tailWord_3613089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613089).length < 2 ^ (prefixWord ++ tailWord_3613089).sum := by decide
  have hdescent : baseEnd_3613089 < baseStart_3613089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3613101 : List Nat := [1, 5, 2, 2, 2, 2, 9]
def baseStart_3613101 : Nat := 118140960795 + 3613101 * 2 ^ 59
def prefixEnd_3613101 : Nat := 4983230072969 + 3 ^ 40 * 3613101 * 2
def baseEnd_3613101 : Nat := 22904413163463869869397

theorem tailTrace_3613101 : CollatzResearch.WordTrace tailWord_3613101 prefixEnd_3613101 22904413163463869869397 := by
  unfold tailWord_3613101
  simp only [CollatzResearch.WordTrace]
  refine ⟨131780619683359620368575157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87853746455573080245716771 131780619683359620368575157)
  ·
    refine ⟨12354433095314964409553921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 131780619683359620368575157 12354433095314964409553921)
    ·
      refine ⟨9265824821486223307165441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12354433095314964409553921 9265824821486223307165441)
      ·
        refine ⟨6949368616114667480374081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9265824821486223307165441 6949368616114667480374081)
        ·
          refine ⟨5212026462086000610280561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6949368616114667480374081 5212026462086000610280561)
          ·
            refine ⟨3909019846564500457710421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5212026462086000610280561 3909019846564500457710421)
            ·
              refine ⟨22904413163463869869397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3909019846564500457710421 22904413163463869869397)
              ·
                rfl

theorem cell23_3613101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 9].length) (baseStart_3613101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3613101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3613101 prefixEnd_3613101 := by exact prefixLift 3613101
  have htrace : WordTrace (prefixWord ++ tailWord_3613101) baseStart_3613101 baseEnd_3613101 := by
    simpa [prefixWord, tailWord_3613101, baseEnd_3613101] using wordTrace_append hprefix tailTrace_3613101
  have hstable : (prefixWord ++ tailWord_3613101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3613101).length < 2 ^ (prefixWord ++ tailWord_3613101).sum := by decide
  have hdescent : baseEnd_3613101 < baseStart_3613101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3613101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
