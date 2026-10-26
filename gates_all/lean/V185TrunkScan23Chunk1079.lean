import V185TrunkScan23Chunk1078

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6387762 : List Nat := [3, 2, 1, 1, 2, 4, 10]
def baseStart_6387762 : Nat := 118140960795 + 6387762 * 2 ^ 59
def prefixEnd_6387762 : Nat := 4983230072969 + 3 ^ 40 * 6387762 * 2
def baseEnd_6387762 : Nat := 40493731018831383771583

theorem tailTrace_6387762 : CollatzResearch.WordTrace tailWord_6387762 prefixEnd_6387762 40493731018831383771583 := by
  unfold tailWord_6387762
  simp only [CollatzResearch.WordTrace]
  refine ⟨58245205071059172935077385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155320546856157794493539693 58245205071059172935077385)
  ·
    refine ⟨43683903803294379701308039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58245205071059172935077385 43683903803294379701308039)
    ·
      refine ⟨65525855704941569551962059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43683903803294379701308039 65525855704941569551962059)
      ·
        refine ⟨98288783557412354327943089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65525855704941569551962059 98288783557412354327943089)
        ·
          refine ⟨73716587668059265745957317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98288783557412354327943089 73716587668059265745957317)
          ·
            refine ⟨13821860187761112327366997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73716587668059265745957317 13821860187761112327366997)
            ·
              refine ⟨40493731018831383771583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13821860187761112327366997 40493731018831383771583)
              ·
                rfl

theorem cell23_6387762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 10].length) (baseStart_6387762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6387762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6387762 prefixEnd_6387762 := by exact prefixLift 6387762
  have htrace : WordTrace (prefixWord ++ tailWord_6387762) baseStart_6387762 baseEnd_6387762 := by
    simpa [prefixWord, tailWord_6387762, baseEnd_6387762] using wordTrace_append hprefix tailTrace_6387762
  have hstable : (prefixWord ++ tailWord_6387762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6387762).length < 2 ^ (prefixWord ++ tailWord_6387762).sum := by decide
  have hdescent : baseEnd_6387762 < baseStart_6387762 := by decide
  rcases family_descends (prefixWord ++ tailWord_6387762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6387766 : List Nat := [5, 1, 2, 1, 1, 1, 3, 1, 4, 4]
def baseStart_6387766 : Nat := 118140960795 + 6387766 * 2 ^ 59
def prefixEnd_6387766 : Nat := 4983230072969 + 3 ^ 40 * 6387766 * 2
def baseEnd_6387766 : Nat := 1093331422149320023282735

theorem tailTrace_6387766 : CollatzResearch.WordTrace tailWord_6387766 prefixEnd_6387766 1093331422149320023282735 := by
  unfold tailWord_6387766
  simp only [CollatzResearch.WordTrace]
  refine ⟨14561310386013887526465947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 155320644117481466948970101 14561310386013887526465947)
  ·
    refine ⟨21841965579020831289698921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14561310386013887526465947 21841965579020831289698921)
    ·
      refine ⟨16381474184265623467274191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21841965579020831289698921 16381474184265623467274191)
      ·
        refine ⟨24572211276398435200911287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16381474184265623467274191 24572211276398435200911287)
        ·
          refine ⟨36858316914597652801366931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24572211276398435200911287 36858316914597652801366931)
          ·
            refine ⟨55287475371896479202050397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36858316914597652801366931 55287475371896479202050397)
            ·
              refine ⟨20732803264461179700768899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55287475371896479202050397 20732803264461179700768899)
              ·
                refine ⟨31099204896691769551153349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20732803264461179700768899 31099204896691769551153349)
                ·
                  refine ⟨5831100918129706790841253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31099204896691769551153349 5831100918129706790841253)
                  ·
                    refine ⟨1093331422149320023282735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5831100918129706790841253 1093331422149320023282735)
                    ·
                      rfl

theorem cell23_6387766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_6387766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6387766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6387766 prefixEnd_6387766 := by exact prefixLift 6387766
  have htrace : WordTrace (prefixWord ++ tailWord_6387766) baseStart_6387766 baseEnd_6387766 := by
    simpa [prefixWord, tailWord_6387766, baseEnd_6387766] using wordTrace_append hprefix tailTrace_6387766
  have hstable : (prefixWord ++ tailWord_6387766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6387766).length < 2 ^ (prefixWord ++ tailWord_6387766).sum := by decide
  have hdescent : baseEnd_6387766 < baseStart_6387766 := by decide
  rcases family_descends (prefixWord ++ tailWord_6387766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6387773 : List Nat := [1, 4, 1, 3, 1, 1, 4, 1, 3, 2, 2]
def baseStart_6387773 : Nat := 118140960795 + 6387773 * 2 ^ 59
def prefixEnd_6387773 : Nat := 4983230072969 + 3 ^ 40 * 6387773 * 2
def baseEnd_6387773 : Nat := 3279997860812541542460673

theorem tailTrace_6387773 : CollatzResearch.WordTrace tailWord_6387773 prefixEnd_6387773 3279997860812541542460673 := by
  unfold tailWord_6387773
  simp only [CollatzResearch.WordTrace]
  refine ⟨232981221487196840618959973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155320814324797893745973315 232981221487196840618959973)
  ·
    refine ⟨43683979028849407616054995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 232981221487196840618959973 43683979028849407616054995)
    ·
      refine ⟨65525968543274111424082493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43683979028849407616054995 65525968543274111424082493)
      ·
        refine ⟨24572238203727791784030935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65525968543274111424082493 24572238203727791784030935)
        ·
          refine ⟨36858357305591687676046403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24572238203727791784030935 36858357305591687676046403)
          ·
            refine ⟨55287535958387531514069605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36858357305591687676046403 55287535958387531514069605)
            ·
              refine ⟨10366412992197662158888051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55287535958387531514069605 10366412992197662158888051)
              ·
                refine ⟨15549619488296493238332077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10366412992197662158888051 15549619488296493238332077)
                ·
                  refine ⟨5831107308111184964374529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15549619488296493238332077 5831107308111184964374529)
                  ·
                    refine ⟨4373330481083388723280897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5831107308111184964374529 4373330481083388723280897)
                    ·
                      refine ⟨3279997860812541542460673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4373330481083388723280897 3279997860812541542460673)
                      ·
                        rfl

theorem cell23_6387773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_6387773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6387773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6387773 prefixEnd_6387773 := by exact prefixLift 6387773
  have htrace : WordTrace (prefixWord ++ tailWord_6387773) baseStart_6387773 baseEnd_6387773 := by
    simpa [prefixWord, tailWord_6387773, baseEnd_6387773] using wordTrace_append hprefix tailTrace_6387773
  have hstable : (prefixWord ++ tailWord_6387773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6387773).length < 2 ^ (prefixWord ++ tailWord_6387773).sum := by decide
  have hdescent : baseEnd_6387773 < baseStart_6387773 := by decide
  rcases family_descends (prefixWord ++ tailWord_6387773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6387802 : List Nat := [3, 1, 1, 2, 1, 1, 3, 1, 1, 4, 5]
def baseStart_6387802 : Nat := 118140960795 + 6387802 * 2 ^ 59
def prefixEnd_6387802 : Nat := 4983230072969 + 3 ^ 40 * 6387802 * 2
def baseEnd_6387802 : Nat := 3280012751751521928998039

theorem tailTrace_6387802 : CollatzResearch.WordTrace tailWord_6387802 prefixEnd_6387802 3280012751751521928998039 := by
  unfold tailWord_6387802
  simp only [CollatzResearch.WordTrace]
  refine ⟨58245569801022944642941415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155321519469394519047843773 58245569801022944642941415)
  ·
    refine ⟨87368354701534416964412123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58245569801022944642941415 87368354701534416964412123)
    ·
      refine ⟨131052532052301625446618185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87368354701534416964412123 131052532052301625446618185)
      ·
        refine ⟨98289399039226219084963639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131052532052301625446618185 98289399039226219084963639)
        ·
          refine ⟨147434098558839328627445459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98289399039226219084963639 147434098558839328627445459)
          ·
            refine ⟨221151147838258992941168189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147434098558839328627445459 221151147838258992941168189)
            ·
              refine ⟨82931680439347122352938071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 221151147838258992941168189 82931680439347122352938071)
              ·
                refine ⟨124397520659020683529407107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82931680439347122352938071 124397520659020683529407107)
                ·
                  refine ⟨186596280988531025294110661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124397520659020683529407107 186596280988531025294110661)
                  ·
                    refine ⟨34986802685349567242645749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 186596280988531025294110661 34986802685349567242645749)
                    ·
                      refine ⟨3280012751751521928998039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34986802685349567242645749 3280012751751521928998039)
                      ·
                        rfl

theorem cell23_6387802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_6387802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6387802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6387802 prefixEnd_6387802 := by exact prefixLift 6387802
  have htrace : WordTrace (prefixWord ++ tailWord_6387802) baseStart_6387802 baseEnd_6387802 := by
    simpa [prefixWord, tailWord_6387802, baseEnd_6387802] using wordTrace_append hprefix tailTrace_6387802
  have hstable : (prefixWord ++ tailWord_6387802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6387802).length < 2 ^ (prefixWord ++ tailWord_6387802).sum := by decide
  have hdescent : baseEnd_6387802 < baseStart_6387802 := by decide
  rcases family_descends (prefixWord ++ tailWord_6387802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6387832 : List Nat := [2, 1, 2, 1, 1, 1, 3, 1, 3, 3, 5]
def baseStart_6387832 : Nat := 118140960795 + 6387832 * 2 ^ 59
def prefixEnd_6387832 : Nat := 4983230072969 + 3 ^ 40 * 6387832 * 2
def baseEnd_6387832 : Nat := 3280028156171156811622901

theorem tailTrace_6387832 : CollatzResearch.WordTrace tailWord_6387832 prefixEnd_6387832 3280028156171156811622901 := by
  unfold tailWord_6387832
  simp only [CollatzResearch.WordTrace]
  refine ⟨116491686696991546847678875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155322248929322062463571833 116491686696991546847678875)
  ·
    refine ⟨174737530045487320271518313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116491686696991546847678875 174737530045487320271518313)
    ·
      refine ⟨131053147534115490203638735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174737530045487320271518313 131053147534115490203638735)
      ·
        refine ⟨196579721301173235305458103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131053147534115490203638735 196579721301173235305458103)
        ·
          refine ⟨294869581951759852958187155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196579721301173235305458103 294869581951759852958187155)
          ·
            refine ⟨442304372927639779437280733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294869581951759852958187155 442304372927639779437280733)
            ·
              refine ⟨165864139847864917288980275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 442304372927639779437280733 165864139847864917288980275)
              ·
                refine ⟨248796209771797375933470413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165864139847864917288980275 248796209771797375933470413)
                ·
                  refine ⟨93298578664424015975051405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 248796209771797375933470413 93298578664424015975051405)
                  ·
                    refine ⟨34986966999159005990644277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 93298578664424015975051405 34986966999159005990644277)
                    ·
                      refine ⟨3280028156171156811622901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34986966999159005990644277 3280028156171156811622901)
                      ·
                        rfl

theorem cell23_6387832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 3, 3, 5].length) (baseStart_6387832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6387832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6387832 prefixEnd_6387832 := by exact prefixLift 6387832
  have htrace : WordTrace (prefixWord ++ tailWord_6387832) baseStart_6387832 baseEnd_6387832 := by
    simpa [prefixWord, tailWord_6387832, baseEnd_6387832] using wordTrace_append hprefix tailTrace_6387832
  have hstable : (prefixWord ++ tailWord_6387832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6387832).length < 2 ^ (prefixWord ++ tailWord_6387832).sum := by decide
  have hdescent : baseEnd_6387832 < baseStart_6387832 := by decide
  rcases family_descends (prefixWord ++ tailWord_6387832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6387850 : List Nat := [3, 1, 2, 3, 1, 4, 1, 2, 1, 3, 2]
def baseStart_6387850 : Nat := 118140960795 + 6387850 * 2 ^ 59
def prefixEnd_6387850 : Nat := 4983230072969 + 3 ^ 40 * 6387850 * 2
def baseEnd_6387850 : Nat := 3280037398822937741197819

theorem tailTrace_6387850 : CollatzResearch.WordTrace tailWord_6387850 prefixEnd_6387850 3280037398822937741197819 := by
  unfold tailWord_6387850
  simp only [CollatzResearch.WordTrace]
  refine ⟨58246007476979470692378251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155322686605278588513008669 58246007476979470692378251)
  ·
    refine ⟨87369011215469206038567377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58246007476979470692378251 87369011215469206038567377)
    ·
      refine ⟨65526758411601904528925533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87369011215469206038567377 65526758411601904528925533)
      ·
        refine ⟨24572534404350714198347075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65526758411601904528925533 24572534404350714198347075)
        ·
          refine ⟨36858801606526071297520613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24572534404350714198347075 36858801606526071297520613)
          ·
            refine ⟨6911025301223638368285115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36858801606526071297520613 6911025301223638368285115)
            ·
              refine ⟨10366537951835457552427673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6911025301223638368285115 10366537951835457552427673)
              ·
                refine ⟨7774903463876593164320755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10366537951835457552427673 7774903463876593164320755)
                ·
                  refine ⟨11662355195814889746481133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7774903463876593164320755 11662355195814889746481133)
                  ·
                    refine ⟨4373383198430583654930425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11662355195814889746481133 4373383198430583654930425)
                    ·
                      refine ⟨3280037398822937741197819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4373383198430583654930425 3280037398822937741197819)
                      ·
                        rfl

theorem cell23_6387850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_6387850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6387850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6387850 prefixEnd_6387850 := by exact prefixLift 6387850
  have htrace : WordTrace (prefixWord ++ tailWord_6387850) baseStart_6387850 baseEnd_6387850 := by
    simpa [prefixWord, tailWord_6387850, baseEnd_6387850] using wordTrace_append hprefix tailTrace_6387850
  have hstable : (prefixWord ++ tailWord_6387850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6387850).length < 2 ^ (prefixWord ++ tailWord_6387850).sum := by decide
  have hdescent : baseEnd_6387850 < baseStart_6387850 := by decide
  rcases family_descends (prefixWord ++ tailWord_6387850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6387863 : List Nat := [1, 1, 3, 3, 4, 1, 1, 2, 1, 4, 2]
def baseStart_6387863 : Nat := 118140960795 + 6387863 * 2 ^ 59
def prefixEnd_6387863 : Nat := 4983230072969 + 3 ^ 40 * 6387863 * 2
def baseEnd_6387863 : Nat := 3280044074071446190335259

theorem tailTrace_6387863 : CollatzResearch.WordTrace tailWord_6387863 prefixEnd_6387863 3280044074071446190335259 := by
  unfold tailWord_6387863
  simp only [CollatzResearch.WordTrace]
  refine ⟨232984504056870785989736243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155323002704580523993157495 232984504056870785989736243)
  ·
    refine ⟨349476756085306178984604365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232984504056870785989736243 349476756085306178984604365)
    ·
      refine ⟨131053783531989817119226637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 349476756085306178984604365 131053783531989817119226637)
      ·
        refine ⟨49145168824496181419709989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131053783531989817119226637 49145168824496181419709989)
        ·
          refine ⟨9214719154593034016195623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49145168824496181419709989 9214719154593034016195623)
          ·
            refine ⟨13822078731889551024293435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9214719154593034016195623 13822078731889551024293435)
            ·
              refine ⟨20733118097834326536440153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13822078731889551024293435 20733118097834326536440153)
              ·
                refine ⟨15549838573375744902330115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20733118097834326536440153 15549838573375744902330115)
                ·
                  refine ⟨23324757860063617353495173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15549838573375744902330115 23324757860063617353495173)
                  ·
                    refine ⟨4373392098761928253780345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23324757860063617353495173 4373392098761928253780345)
                    ·
                      refine ⟨3280044074071446190335259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4373392098761928253780345 3280044074071446190335259)
                      ·
                        rfl

theorem cell23_6387863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 2, 1, 4, 2].length) (baseStart_6387863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6387863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6387863 prefixEnd_6387863 := by exact prefixLift 6387863
  have htrace : WordTrace (prefixWord ++ tailWord_6387863) baseStart_6387863 baseEnd_6387863 := by
    simpa [prefixWord, tailWord_6387863, baseEnd_6387863] using wordTrace_append hprefix tailTrace_6387863
  have hstable : (prefixWord ++ tailWord_6387863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6387863).length < 2 ^ (prefixWord ++ tailWord_6387863).sum := by decide
  have hdescent : baseEnd_6387863 < baseStart_6387863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6387863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6387893 : List Nat := [1, 3, 3, 4, 1, 1, 1, 1, 2, 2, 4]
def baseStart_6387893 : Nat := 118140960795 + 6387893 * 2 ^ 59
def prefixEnd_6387893 : Nat := 4983230072969 + 3 ^ 40 * 6387893 * 2
def baseEnd_6387893 : Nat := 3280059478491081072960121

theorem tailTrace_6387893 : CollatzResearch.WordTrace tailWord_6387893 prefixEnd_6387893 3280059478491081072960121 := by
  unfold tailWord_6387893
  simp only [CollatzResearch.WordTrace]
  refine ⟨232985598246762101113328333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155323732164508067408885555 232985598246762101113328333)
  ·
    refine ⟨87369599342535787917498125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232985598246762101113328333 87369599342535787917498125)
    ·
      refine ⟨32763599753450920469061797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87369599342535787917498125 32763599753450920469061797)
      ·
        refine ⟨6143174953772047587949087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32763599753450920469061797 6143174953772047587949087)
        ·
          refine ⟨9214762430658071381923631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6143174953772047587949087 9214762430658071381923631)
          ·
            refine ⟨13822143645987107072885447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9214762430658071381923631 13822143645987107072885447)
            ·
              refine ⟨20733215468980660609328171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13822143645987107072885447 20733215468980660609328171)
              ·
                refine ⟨31099823203470990913992257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20733215468980660609328171 31099823203470990913992257)
                ·
                  refine ⟨23324867402603243185494193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31099823203470990913992257 23324867402603243185494193)
                  ·
                    refine ⟨17493650551952432389120645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23324867402603243185494193 17493650551952432389120645)
                    ·
                      refine ⟨3280059478491081072960121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17493650551952432389120645 3280059478491081072960121)
                      ·
                        rfl

theorem cell23_6387893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_6387893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6387893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6387893 prefixEnd_6387893 := by exact prefixLift 6387893
  have htrace : WordTrace (prefixWord ++ tailWord_6387893) baseStart_6387893 baseEnd_6387893 := by
    simpa [prefixWord, tailWord_6387893, baseEnd_6387893] using wordTrace_append hprefix tailTrace_6387893
  have hstable : (prefixWord ++ tailWord_6387893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6387893).length < 2 ^ (prefixWord ++ tailWord_6387893).sum := by decide
  have hdescent : baseEnd_6387893 < baseStart_6387893 := by decide
  rcases family_descends (prefixWord ++ tailWord_6387893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6387919 : List Nat := [1, 1, 2, 1, 1, 3, 5, 1, 1, 3, 4]
def baseStart_6387919 : Nat := 118140960795 + 6387919 * 2 ^ 59
def prefixEnd_6387919 : Nat := 4983230072969 + 3 ^ 40 * 6387919 * 2
def baseEnd_6387919 : Nat := 3280072828988097971235001

theorem tailTrace_6387919 : CollatzResearch.WordTrace tailWord_6387919 prefixEnd_6387919 3280072828988097971235001 := by
  unfold tailWord_6387919
  simp only [CollatzResearch.WordTrace]
  refine ⟨232986546544667907553774811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155324364363111938369183207 232986546544667907553774811)
  ·
    refine ⟨349479819817001861330662217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232986546544667907553774811 349479819817001861330662217)
    ·
      refine ⟨262109864862751395997996663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 349479819817001861330662217 262109864862751395997996663)
      ·
        refine ⟨393164797294127093996994995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262109864862751395997996663 393164797294127093996994995)
        ·
          refine ⟨589747195941190640995492493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 393164797294127093996994995 589747195941190640995492493)
          ·
            refine ⟨221155198477946490373309685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 589747195941190640995492493 221155198477946490373309685)
            ·
              refine ⟨20733299857307483472497783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 221155198477946490373309685 20733299857307483472497783)
              ·
                refine ⟨31099949785961225208746675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20733299857307483472497783 31099949785961225208746675)
                ·
                  refine ⟨46649924678941837813120013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31099949785961225208746675 46649924678941837813120013)
                  ·
                    refine ⟨17493721754603189179920005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46649924678941837813120013 17493721754603189179920005)
                    ·
                      refine ⟨3280072828988097971235001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17493721754603189179920005 3280072828988097971235001)
                      ·
                        rfl

theorem cell23_6387919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 3, 4].length) (baseStart_6387919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6387919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6387919 prefixEnd_6387919 := by exact prefixLift 6387919
  have htrace : WordTrace (prefixWord ++ tailWord_6387919) baseStart_6387919 baseEnd_6387919 := by
    simpa [prefixWord, tailWord_6387919, baseEnd_6387919] using wordTrace_append hprefix tailTrace_6387919
  have hstable : (prefixWord ++ tailWord_6387919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6387919).length < 2 ^ (prefixWord ++ tailWord_6387919).sum := by decide
  have hdescent : baseEnd_6387919 < baseStart_6387919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6387919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6387936 : List Nat := [2, 1, 1, 3, 1, 3, 1, 1, 4, 4, 2]
def baseStart_6387936 : Nat := 118140960795 + 6387936 * 2 ^ 59
def prefixEnd_6387936 : Nat := 4983230072969 + 3 ^ 40 * 6387936 * 2
def baseEnd_6387936 : Nat := 3280081558159224404722423

theorem tailTrace_6387936 : CollatzResearch.WordTrace tailWord_6387936 prefixEnd_6387936 3280081558159224404722423 := by
  unfold tailWord_6387936
  simp only [CollatzResearch.WordTrace]
  refine ⟨116493583292803159728571831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155324777723737546304762441 116493583292803159728571831)
  ·
    refine ⟨174740374939204739592857747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116493583292803159728571831 174740374939204739592857747)
    ·
      refine ⟨262110562408807109389286621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174740374939204739592857747 262110562408807109389286621)
      ·
        refine ⟨98291460903302666020982483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 262110562408807109389286621 98291460903302666020982483)
        ·
          refine ⟨147437191354953999031473725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98291460903302666020982483 147437191354953999031473725)
          ·
            refine ⟨55288946758107749636802647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147437191354953999031473725 55288946758107749636802647)
            ·
              refine ⟨82933420137161624455203971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55288946758107749636802647 82933420137161624455203971)
              ·
                refine ⟨124400130205742436682805957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82933420137161624455203971 124400130205742436682805957)
                ·
                  refine ⟨23325024413576706878026117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 124400130205742436682805957 23325024413576706878026117)
                  ·
                    refine ⟨4373442077545632539629897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23325024413576706878026117 4373442077545632539629897)
                    ·
                      refine ⟨3280081558159224404722423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4373442077545632539629897 3280081558159224404722423)
                      ·
                        rfl

theorem cell23_6387936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 4, 4, 2].length) (baseStart_6387936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6387936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6387936 prefixEnd_6387936 := by exact prefixLift 6387936
  have htrace : WordTrace (prefixWord ++ tailWord_6387936) baseStart_6387936 baseEnd_6387936 := by
    simpa [prefixWord, tailWord_6387936, baseEnd_6387936] using wordTrace_append hprefix tailTrace_6387936
  have hstable : (prefixWord ++ tailWord_6387936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6387936).length < 2 ^ (prefixWord ++ tailWord_6387936).sum := by decide
  have hdescent : baseEnd_6387936 < baseStart_6387936 := by decide
  rcases family_descends (prefixWord ++ tailWord_6387936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6387966 : List Nat := [4, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4]
def baseStart_6387966 : Nat := 118140960795 + 6387966 * 2 ^ 59
def prefixEnd_6387966 : Nat := 4983230072969 + 3 ^ 40 * 6387966 * 2
def baseEnd_6387966 : Nat := 3280096962578859287347285

theorem tailTrace_6387966 : CollatzResearch.WordTrace tailWord_6387966 prefixEnd_6387966 3280096962578859287347285 := by
  unfold tailWord_6387966
  simp only [CollatzResearch.WordTrace]
  refine ⟨29123532596937204322591969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155325507183665089720490501 29123532596937204322591969)
  ·
    refine ⟨21842649447702903241943977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29123532596937204322591969 21842649447702903241943977)
    ·
      refine ⟨16381987085777177431457983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21842649447702903241943977 16381987085777177431457983)
      ·
        refine ⟨24572980628665766147186975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16381987085777177431457983 24572980628665766147186975)
        ·
          refine ⟨36859470942998649220780463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24572980628665766147186975 36859470942998649220780463)
          ·
            refine ⟨55289206414497973831170695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36859470942998649220780463 55289206414497973831170695)
            ·
              refine ⟨82933809621746960746756043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55289206414497973831170695 82933809621746960746756043)
              ·
                refine ⟨124400714432620441120134065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82933809621746960746756043 124400714432620441120134065)
                ·
                  refine ⟨93300535824465330840100549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124400714432620441120134065 93300535824465330840100549)
                  ·
                    refine ⟨17493850467087249532518853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 93300535824465330840100549 17493850467087249532518853)
                    ·
                      refine ⟨3280096962578859287347285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17493850467087249532518853 3280096962578859287347285)
                      ·
                        rfl

theorem cell23_6387966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_6387966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6387966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6387966 prefixEnd_6387966 := by exact prefixLift 6387966
  have htrace : WordTrace (prefixWord ++ tailWord_6387966) baseStart_6387966 baseEnd_6387966 := by
    simpa [prefixWord, tailWord_6387966, baseEnd_6387966] using wordTrace_append hprefix tailTrace_6387966
  have hstable : (prefixWord ++ tailWord_6387966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6387966).length < 2 ^ (prefixWord ++ tailWord_6387966).sum := by decide
  have hdescent : baseEnd_6387966 < baseStart_6387966 := by decide
  rcases family_descends (prefixWord ++ tailWord_6387966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6387997 : List Nat := [1, 4, 2, 3, 3, 1, 1, 1, 3, 4]
def baseStart_6387997 : Nat := 118140960795 + 6387997 * 2 ^ 59
def prefixEnd_6387997 : Nat := 4983230072969 + 3 ^ 40 * 6387997 * 2
def baseEnd_6387997 : Nat := 1093370960159716222019881

theorem tailTrace_6387997 : CollatzResearch.WordTrace tailWord_6387997 prefixEnd_6387997 1093370960159716222019881 := by
  unfold tailWord_6387997
  simp only [CollatzResearch.WordTrace]
  refine ⟨232989391438385326875114245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155326260958923551250076163 232989391438385326875114245)
  ·
    refine ⟨43685510894697248789083921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 232989391438385326875114245 43685510894697248789083921)
    ·
      refine ⟨32764133171022936591812941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43685510894697248789083921 32764133171022936591812941)
      ·
        refine ⟨12286549939133601221929853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32764133171022936591812941 12286549939133601221929853)
        ·
          refine ⟨4607456227175100458223695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12286549939133601221929853 4607456227175100458223695)
          ·
            refine ⟨6911184340762650687335543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4607456227175100458223695 6911184340762650687335543)
            ·
              refine ⟨10366776511143976031003315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6911184340762650687335543 10366776511143976031003315)
              ·
                refine ⟨15550164766715964046504973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10366776511143976031003315 15550164766715964046504973)
                ·
                  refine ⟨5831311787518486517439365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15550164766715964046504973 5831311787518486517439365)
                  ·
                    refine ⟨1093370960159716222019881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5831311787518486517439365 1093370960159716222019881)
                    ·
                      rfl

theorem cell23_6387997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 1, 3, 4].length) (baseStart_6387997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6387997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6387997 prefixEnd_6387997 := by exact prefixLift 6387997
  have htrace : WordTrace (prefixWord ++ tailWord_6387997) baseStart_6387997 baseEnd_6387997 := by
    simpa [prefixWord, tailWord_6387997, baseEnd_6387997] using wordTrace_append hprefix tailTrace_6387997
  have hstable : (prefixWord ++ tailWord_6387997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6387997).length < 2 ^ (prefixWord ++ tailWord_6387997).sum := by decide
  have hdescent : baseEnd_6387997 < baseStart_6387997 := by decide
  rcases family_descends (prefixWord ++ tailWord_6387997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6388030 : List Nat := [4, 2, 1, 2, 1, 2, 1, 3, 2, 3, 2]
def baseStart_6388030 : Nat := 118140960795 + 6388030 * 2 ^ 59
def prefixEnd_6388030 : Nat := 4983230072969 + 3 ^ 40 * 6388030 * 2
def baseEnd_6388030 : Nat := 3280129825340747036946991

theorem tailTrace_6388030 : CollatzResearch.WordTrace tailWord_6388030 prefixEnd_6388030 3280129825340747036946991 := by
  unfold tailWord_6388030
  simp only [CollatzResearch.WordTrace]
  refine ⟨29123824380908221688883193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155327063364843849007377029 29123824380908221688883193)
  ·
    refine ⟨21842868285681166266662395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29123824380908221688883193 21842868285681166266662395)
    ·
      refine ⟨32764302428521749399993593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21842868285681166266662395 32764302428521749399993593)
      ·
        refine ⟨24573226821391312049995195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32764302428521749399993593 24573226821391312049995195)
        ·
          refine ⟨36859840232086968074992793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24573226821391312049995195 36859840232086968074992793)
          ·
            refine ⟨27644880174065226056244595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36859840232086968074992793 27644880174065226056244595)
            ·
              refine ⟨41467320261097839084366893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27644880174065226056244595 41467320261097839084366893)
              ·
                refine ⟨15550245097911689656637585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41467320261097839084366893 15550245097911689656637585)
                ·
                  refine ⟨11662683823433767242478189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15550245097911689656637585 11662683823433767242478189)
                  ·
                    refine ⟨4373506433787662715929321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11662683823433767242478189 4373506433787662715929321)
                    ·
                      refine ⟨3280129825340747036946991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4373506433787662715929321 3280129825340747036946991)
                      ·
                        rfl

theorem cell23_6388030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_6388030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6388030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6388030 prefixEnd_6388030 := by exact prefixLift 6388030
  have htrace : WordTrace (prefixWord ++ tailWord_6388030) baseStart_6388030 baseEnd_6388030 := by
    simpa [prefixWord, tailWord_6388030, baseEnd_6388030] using wordTrace_append hprefix tailTrace_6388030
  have hstable : (prefixWord ++ tailWord_6388030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6388030).length < 2 ^ (prefixWord ++ tailWord_6388030).sum := by decide
  have hdescent : baseEnd_6388030 < baseStart_6388030 := by decide
  rcases family_descends (prefixWord ++ tailWord_6388030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6388043 : List Nat := [1, 1, 1, 1, 3, 1, 1, 3, 7, 2, 2]
def baseStart_6388043 : Nat := 118140960795 + 6388043 * 2 ^ 59
def prefixEnd_6388043 : Nat := 4983230072969 + 3 ^ 40 * 6388043 * 2
def baseEnd_6388043 : Nat := 3280136500589255486084431

theorem tailTrace_6388043 : CollatzResearch.WordTrace tailWord_6388043 prefixEnd_6388043 3280136500589255486084431 := by
  unfold tailWord_6388043
  simp only [CollatzResearch.WordTrace]
  refine ⟨232991069196218676731288783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155327379464145784487525855 232991069196218676731288783)
  ·
    refine ⟨349486603794328015096933175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232991069196218676731288783 349486603794328015096933175)
    ·
      refine ⟨524229905691492022645399763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349486603794328015096933175 524229905691492022645399763)
      ·
        refine ⟨786344858537238033968099645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 524229905691492022645399763 786344858537238033968099645)
        ·
          refine ⟨294879321951464262738037367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 786344858537238033968099645 294879321951464262738037367)
          ·
            refine ⟨442318982927196394107056051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294879321951464262738037367 442318982927196394107056051)
            ·
              refine ⟨663478474390794591160584077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 442318982927196394107056051 663478474390794591160584077)
              ·
                refine ⟨248804427896547971685219029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 663478474390794591160584077 248804427896547971685219029)
                ·
                  refine ⟨5831353778825343086372321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 248804427896547971685219029 5831353778825343086372321)
                  ·
                    refine ⟨4373515334119007314779241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5831353778825343086372321 4373515334119007314779241)
                    ·
                      refine ⟨3280136500589255486084431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4373515334119007314779241 3280136500589255486084431)
                      ·
                        rfl

theorem cell23_6388043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 7, 2, 2].length) (baseStart_6388043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6388043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6388043 prefixEnd_6388043 := by exact prefixLift 6388043
  have htrace : WordTrace (prefixWord ++ tailWord_6388043) baseStart_6388043 baseEnd_6388043 := by
    simpa [prefixWord, tailWord_6388043, baseEnd_6388043] using wordTrace_append hprefix tailTrace_6388043
  have hstable : (prefixWord ++ tailWord_6388043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6388043).length < 2 ^ (prefixWord ++ tailWord_6388043).sum := by decide
  have hdescent : baseEnd_6388043 < baseStart_6388043 := by decide
  rcases family_descends (prefixWord ++ tailWord_6388043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6388046 : List Nat := [4, 1, 1, 1, 1, 1, 2, 5, 1, 1, 5]
def baseStart_6388046 : Nat := 118140960795 + 6388046 * 2 ^ 59
def prefixEnd_6388046 : Nat := 4983230072969 + 3 ^ 40 * 6388046 * 2
def baseEnd_6388046 : Nat := 3280138041031218974346917

theorem tailTrace_6388046 : CollatzResearch.WordTrace tailWord_6388046 prefixEnd_6388046 3280138041031218974346917 := by
  unfold tailWord_6388046
  simp only [CollatzResearch.WordTrace]
  refine ⟨29123897326900976030455999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155327452410138538829098661 29123897326900976030455999)
  ·
    refine ⟨43685845990351464045683999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29123897326900976030455999 43685845990351464045683999)
    ·
      refine ⟨65528768985527196068525999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43685845990351464045683999 65528768985527196068525999)
      ·
        refine ⟨98293153478290794102788999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65528768985527196068525999 98293153478290794102788999)
        ·
          refine ⟨147439730217436191154183499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98293153478290794102788999 147439730217436191154183499)
          ·
            refine ⟨221159595326154286731275249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147439730217436191154183499 221159595326154286731275249)
            ·
              refine ⟨165869696494615715048456437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221159595326154286731275249 165869696494615715048456437)
              ·
                refine ⟨15550284046370223285792791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 165869696494615715048456437 15550284046370223285792791)
                ·
                  refine ⟨23325426069555334928689187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15550284046370223285792791 23325426069555334928689187)
                  ·
                    refine ⟨34988139104333002393033781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23325426069555334928689187 34988139104333002393033781)
                    ·
                      refine ⟨3280138041031218974346917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34988139104333002393033781 3280138041031218974346917)
                      ·
                        rfl

theorem cell23_6388046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 5, 1, 1, 5].length) (baseStart_6388046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6388046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6388046 prefixEnd_6388046 := by exact prefixLift 6388046
  have htrace : WordTrace (prefixWord ++ tailWord_6388046) baseStart_6388046 baseEnd_6388046 := by
    simpa [prefixWord, tailWord_6388046, baseEnd_6388046] using wordTrace_append hprefix tailTrace_6388046
  have hstable : (prefixWord ++ tailWord_6388046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6388046).length < 2 ^ (prefixWord ++ tailWord_6388046).sum := by decide
  have hdescent : baseEnd_6388046 < baseStart_6388046 := by decide
  rcases family_descends (prefixWord ++ tailWord_6388046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6388049 : List Nat := [1, 2, 2, 1, 4, 13]
def baseStart_6388049 : Nat := 118140960795 + 6388049 * 2 ^ 59
def prefixEnd_6388049 : Nat := 4983230072969 + 3 ^ 40 * 6388049 * 2
def baseEnd_6388049 : Nat := 13498516796185936060121

theorem tailTrace_6388049 : CollatzResearch.WordTrace tailWord_6388049 prefixEnd_6388049 13498516796185936060121 := by
  unfold tailWord_6388049
  simp only [CollatzResearch.WordTrace]
  refine ⟨232991288034196939756007201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155327525356131293170671467 232991288034196939756007201)
  ·
    refine ⟨174743466025647704817005401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232991288034196939756007201 174743466025647704817005401)
    ·
      refine ⟨131057599519235778612754051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174743466025647704817005401 131057599519235778612754051)
      ·
        refine ⟨196586399278853667919131077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131057599519235778612754051 196586399278853667919131077)
        ·
          refine ⟨36859949864785062734837077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 196586399278853667919131077 36859949864785062734837077)
          ·
            refine ⟨13498516796185936060121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 36859949864785062734837077 13498516796185936060121)
            ·
              rfl

theorem cell23_6388049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 13].length) (baseStart_6388049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6388049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6388049 prefixEnd_6388049 := by exact prefixLift 6388049
  have htrace : WordTrace (prefixWord ++ tailWord_6388049) baseStart_6388049 baseEnd_6388049 := by
    simpa [prefixWord, tailWord_6388049, baseEnd_6388049] using wordTrace_append hprefix tailTrace_6388049
  have hstable : (prefixWord ++ tailWord_6388049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6388049).length < 2 ^ (prefixWord ++ tailWord_6388049).sum := by decide
  have hdescent : baseEnd_6388049 < baseStart_6388049 := by decide
  rcases family_descends (prefixWord ++ tailWord_6388049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6388093 : List Nat := [1, 4, 1, 1, 2, 3, 2, 2, 1, 3, 3]
def baseStart_6388093 : Nat := 118140960795 + 6388093 * 2 ^ 59
def prefixEnd_6388093 : Nat := 4983230072969 + 3 ^ 40 * 6388093 * 2
def baseEnd_6388093 : Nat := 3280162174621980290459201

theorem tailTrace_6388093 : CollatzResearch.WordTrace tailWord_6388093 prefixEnd_6388093 3280162174621980290459201 := by
  unfold tailWord_6388093
  simp only [CollatzResearch.WordTrace]
  refine ⟨232992892846037535270608933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155328595230691690180405955 232992892846037535270608933)
  ·
    refine ⟨43686167408632037863239175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 232992892846037535270608933 43686167408632037863239175)
    ·
      refine ⟨65529251112948056794858763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43686167408632037863239175 65529251112948056794858763)
      ·
        refine ⟨98293876669422085192288145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65529251112948056794858763 98293876669422085192288145)
        ·
          refine ⟨73720407502066563894216109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98293876669422085192288145 73720407502066563894216109)
          ·
            refine ⟨27645152813274961460331041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73720407502066563894216109 27645152813274961460331041)
            ·
              refine ⟨20733864609956221095248281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27645152813274961460331041 20733864609956221095248281)
              ·
                refine ⟨15550398457467165821436211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20733864609956221095248281 15550398457467165821436211)
                ·
                  refine ⟨23325597686200748732154317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15550398457467165821436211 23325597686200748732154317)
                  ·
                    refine ⟨8747099132325280774557869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23325597686200748732154317 8747099132325280774557869)
                    ·
                      refine ⟨3280162174621980290459201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8747099132325280774557869 3280162174621980290459201)
                      ·
                        rfl

theorem cell23_6388093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 2, 1, 3, 3].length) (baseStart_6388093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6388093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6388093 prefixEnd_6388093 := by exact prefixLift 6388093
  have htrace : WordTrace (prefixWord ++ tailWord_6388093) baseStart_6388093 baseEnd_6388093 := by
    simpa [prefixWord, tailWord_6388093, baseEnd_6388093] using wordTrace_append hprefix tailTrace_6388093
  have hstable : (prefixWord ++ tailWord_6388093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6388093).length < 2 ^ (prefixWord ++ tailWord_6388093).sum := by decide
  have hdescent : baseEnd_6388093 < baseStart_6388093 := by decide
  rcases family_descends (prefixWord ++ tailWord_6388093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6388097 : List Nat := [1, 2, 4, 3, 1, 1, 4, 1, 1, 2, 3]
def baseStart_6388097 : Nat := 118140960795 + 6388097 * 2 ^ 59
def prefixEnd_6388097 : Nat := 4983230072969 + 3 ^ 40 * 6388097 * 2
def baseEnd_6388097 : Nat := 3280164228544598274809183

theorem tailTrace_6388097 : CollatzResearch.WordTrace tailWord_6388097 prefixEnd_6388097 3280164228544598274809183 := by
  unfold tailWord_6388097
  simp only [CollatzResearch.WordTrace]
  refine ⟨232993038738023043953754545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155328692492015362635836363 232993038738023043953754545)
  ·
    refine ⟨174744779053517282965315909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232993038738023043953754545 174744779053517282965315909)
    ·
      refine ⟨32764646072534490555996733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 174744779053517282965315909 32764646072534490555996733)
      ·
        refine ⟨12286742277200433958498775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32764646072534490555996733 12286742277200433958498775)
        ·
          refine ⟨18430113415800650937748163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12286742277200433958498775 18430113415800650937748163)
          ·
            refine ⟨27645170123700976406622245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18430113415800650937748163 27645170123700976406622245)
            ·
              refine ⟨5183469398193933076241671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27645170123700976406622245 5183469398193933076241671)
              ·
                refine ⟨7775204097290899614362507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5183469398193933076241671 7775204097290899614362507)
                ·
                  refine ⟨11662806145936349421543761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7775204097290899614362507 11662806145936349421543761)
                  ·
                    refine ⟨8747104609452262066157821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11662806145936349421543761 8747104609452262066157821)
                    ·
                      refine ⟨3280164228544598274809183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8747104609452262066157821 3280164228544598274809183)
                      ·
                        rfl

theorem cell23_6388097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_6388097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6388097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6388097 prefixEnd_6388097 := by exact prefixLift 6388097
  have htrace : WordTrace (prefixWord ++ tailWord_6388097) baseStart_6388097 baseEnd_6388097 := by
    simpa [prefixWord, tailWord_6388097, baseEnd_6388097] using wordTrace_append hprefix tailTrace_6388097
  have hstable : (prefixWord ++ tailWord_6388097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6388097).length < 2 ^ (prefixWord ++ tailWord_6388097).sum := by decide
  have hdescent : baseEnd_6388097 < baseStart_6388097 := by decide
  rcases family_descends (prefixWord ++ tailWord_6388097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6388127 : List Nat := [1, 1, 2, 5, 1, 1, 5, 1, 2, 1, 3]
def baseStart_6388127 : Nat := 118140960795 + 6388127 * 2 ^ 59
def prefixEnd_6388127 : Nat := 4983230072969 + 3 ^ 40 * 6388127 * 2
def baseEnd_6388127 : Nat := 3280179632964233157434045

theorem tailTrace_6388127 : CollatzResearch.WordTrace tailWord_6388127 prefixEnd_6388127 3280179632964233157434045 := by
  unfold tailWord_6388127
  simp only [CollatzResearch.WordTrace]
  refine ⟨232994132927914359077346635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155329421951942906051564423 232994132927914359077346635)
  ·
    refine ⟨349491199391871538616019953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232994132927914359077346635 349491199391871538616019953)
    ·
      refine ⟨262118399543903653962014965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 349491199391871538616019953 262118399543903653962014965)
      ·
        refine ⟨24573599957240967558938903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 262118399543903653962014965 24573599957240967558938903)
        ·
          refine ⟨36860399935861451338408355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24573599957240967558938903 36860399935861451338408355)
          ·
            refine ⟨55290599903792177007612533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36860399935861451338408355 55290599903792177007612533)
            ·
              refine ⟨5183493740980516594463675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55290599903792177007612533 5183493740980516594463675)
              ·
                refine ⟨7775240611470774891695513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5183493740980516594463675 7775240611470774891695513)
                ·
                  refine ⟨5831430458603081168771635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7775240611470774891695513 5831430458603081168771635)
                  ·
                    refine ⟨8747145687904621753157453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5831430458603081168771635 8747145687904621753157453)
                    ·
                      refine ⟨3280179632964233157434045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8747145687904621753157453 3280179632964233157434045)
                      ·
                        rfl

theorem cell23_6388127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_6388127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6388127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6388127 prefixEnd_6388127 := by exact prefixLift 6388127
  have htrace : WordTrace (prefixWord ++ tailWord_6388127) baseStart_6388127 baseEnd_6388127 := by
    simpa [prefixWord, tailWord_6388127, baseEnd_6388127] using wordTrace_append hprefix tailTrace_6388127
  have hstable : (prefixWord ++ tailWord_6388127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6388127).length < 2 ^ (prefixWord ++ tailWord_6388127).sum := by decide
  have hdescent : baseEnd_6388127 < baseStart_6388127 := by decide
  rcases family_descends (prefixWord ++ tailWord_6388127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6388153 : List Nat := [1, 2, 1, 4, 3, 2, 1, 1, 2, 1, 5]
def baseStart_6388153 : Nat := 118140960795 + 6388153 * 2 ^ 59
def prefixEnd_6388153 : Nat := 4983230072969 + 3 ^ 40 * 6388153 * 2
def baseEnd_6388153 : Nat := 3280192983461250055708925

theorem tailTrace_6388153 : CollatzResearch.WordTrace tailWord_6388153 prefixEnd_6388153 3280192983461250055708925 := by
  unfold tailWord_6388153
  simp only [CollatzResearch.WordTrace]
  refine ⟨232995081225820165517793113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155330054150546777011862075 232995081225820165517793113)
  ·
    refine ⟨174746310919365124138344835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232995081225820165517793113 174746310919365124138344835)
    ·
      refine ⟨262119466379047686207517253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174746310919365124138344835 262119466379047686207517253)
      ·
        refine ⟨49147399946071441163909485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 262119466379047686207517253 49147399946071441163909485)
        ·
          refine ⟨18430274979776790436466057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49147399946071441163909485 18430274979776790436466057)
          ·
            refine ⟨13822706234832592827349543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18430274979776790436466057 13822706234832592827349543)
            ·
              refine ⟨20734059352248889241024315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13822706234832592827349543 20734059352248889241024315)
              ·
                refine ⟨31101089028373333861536473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20734059352248889241024315 31101089028373333861536473)
                ·
                  refine ⟨23325816771280000396152355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31101089028373333861536473 23325816771280000396152355)
                  ·
                    refine ⟨34988725156920000594228533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23325816771280000396152355 34988725156920000594228533)
                    ·
                      refine ⟨3280192983461250055708925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34988725156920000594228533 3280192983461250055708925)
                      ·
                        rfl

theorem cell23_6388153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_6388153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6388153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6388153 prefixEnd_6388153 := by exact prefixLift 6388153
  have htrace : WordTrace (prefixWord ++ tailWord_6388153) baseStart_6388153 baseEnd_6388153 := by
    simpa [prefixWord, tailWord_6388153, baseEnd_6388153] using wordTrace_append hprefix tailTrace_6388153
  have hstable : (prefixWord ++ tailWord_6388153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6388153).length < 2 ^ (prefixWord ++ tailWord_6388153).sum := by decide
  have hdescent : baseEnd_6388153 < baseStart_6388153 := by decide
  rcases family_descends (prefixWord ++ tailWord_6388153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6388178 : List Nat := [3, 2, 2, 4, 2, 1, 2, 1, 2, 1, 3]
def baseStart_6388178 : Nat := 118140960795 + 6388178 * 2 ^ 59
def prefixEnd_6388178 : Nat := 4983230072969 + 3 ^ 40 * 6388178 * 2
def baseEnd_6388178 : Nat := 3280205820477612457896311

theorem tailTrace_6388178 : CollatzResearch.WordTrace tailWord_6388178 prefixEnd_6388178 3280205820477612457896311 := by
  unfold tailWord_6388178
  simp only [CollatzResearch.WordTrace]
  refine ⟨58248998262682398696863297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155330662033819729858302125 58248998262682398696863297)
  ·
    refine ⟨43686748697011799022647473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58248998262682398696863297 43686748697011799022647473)
    ·
      refine ⟨32765061522758849266985605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43686748697011799022647473 32765061522758849266985605)
      ·
        refine ⟨6143449035517284237559801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32765061522758849266985605 6143449035517284237559801)
        ·
          refine ⟨4607586776637963178169851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6143449035517284237559801 4607586776637963178169851)
          ·
            refine ⟨6911380164956944767254777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4607586776637963178169851 6911380164956944767254777)
            ·
              refine ⟨5183535123717708575441083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6911380164956944767254777 5183535123717708575441083)
              ·
                refine ⟨7775302685576562863161625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5183535123717708575441083 7775302685576562863161625)
                ·
                  refine ⟨5831477014182422147371219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7775302685576562863161625 5831477014182422147371219)
                  ·
                    refine ⟨8747215521273633221056829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5831477014182422147371219 8747215521273633221056829)
                    ·
                      refine ⟨3280205820477612457896311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8747215521273633221056829 3280205820477612457896311)
                      ·
                        rfl

theorem cell23_6388178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_6388178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6388178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6388178 prefixEnd_6388178 := by exact prefixLift 6388178
  have htrace : WordTrace (prefixWord ++ tailWord_6388178) baseStart_6388178 baseEnd_6388178 := by
    simpa [prefixWord, tailWord_6388178, baseEnd_6388178] using wordTrace_append hprefix tailTrace_6388178
  have hstable : (prefixWord ++ tailWord_6388178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6388178).length < 2 ^ (prefixWord ++ tailWord_6388178).sum := by decide
  have hdescent : baseEnd_6388178 < baseStart_6388178 := by decide
  rcases family_descends (prefixWord ++ tailWord_6388178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6388203 : List Nat := [1, 1, 1, 1, 2, 3, 6, 1, 2, 5]
def baseStart_6388203 : Nat := 118140960795 + 6388203 * 2 ^ 59
def prefixEnd_6388203 : Nat := 4983230072969 + 3 ^ 40 * 6388203 * 2
def baseEnd_6388203 : Nat := 1093406219164658286694565

theorem tailTrace_6388203 : CollatzResearch.WordTrace tailWord_6388203 prefixEnd_6388203 1093406219164658286694565 := by
  unfold tailWord_6388203
  simp only [CollatzResearch.WordTrace]
  refine ⟨232996904875639024057113263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155331269917092682704742175 232996904875639024057113263)
  ·
    refine ⟨349495357313458536085669895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232996904875639024057113263 349495357313458536085669895)
    ·
      refine ⟨524243035970187804128504843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349495357313458536085669895 524243035970187804128504843)
      ·
        refine ⟨786364553955281706192757265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 524243035970187804128504843 786364553955281706192757265)
        ·
          refine ⟨589773415466461279644567949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 786364553955281706192757265 589773415466461279644567949)
          ·
            refine ⟨221165030799922979866712981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 589773415466461279644567949 221165030799922979866712981)
            ·
              refine ⟨10367110818746389681252171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 221165030799922979866712981 10367110818746389681252171)
              ·
                refine ⟨15550666228119584521878257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10367110818746389681252171 15550666228119584521878257)
                ·
                  refine ⟨11662999671089688391408693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15550666228119584521878257 11662999671089688391408693)
                  ·
                    refine ⟨1093406219164658286694565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11662999671089688391408693 1093406219164658286694565)
                    ·
                      rfl

theorem cell23_6388203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 1, 2, 5].length) (baseStart_6388203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6388203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6388203 prefixEnd_6388203 := by exact prefixLift 6388203
  have htrace : WordTrace (prefixWord ++ tailWord_6388203) baseStart_6388203 baseEnd_6388203 := by
    simpa [prefixWord, tailWord_6388203, baseEnd_6388203] using wordTrace_append hprefix tailTrace_6388203
  have hstable : (prefixWord ++ tailWord_6388203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6388203).length < 2 ^ (prefixWord ++ tailWord_6388203).sum := by decide
  have hdescent : baseEnd_6388203 < baseStart_6388203 := by decide
  rcases family_descends (prefixWord ++ tailWord_6388203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6388223 : List Nat := [1, 1, 2, 2, 1, 2, 3, 4, 2, 1, 4]
def baseStart_6388223 : Nat := 118140960795 + 6388223 * 2 ^ 59
def prefixEnd_6388223 : Nat := 4983230072969 + 3 ^ 40 * 6388223 * 2
def baseEnd_6388223 : Nat := 3280228927107064781833603

theorem tailTrace_6388223 : CollatzResearch.WordTrace tailWord_6388223 prefixEnd_6388223 3280228927107064781833603 := by
  unfold tailWord_6388223
  simp only [CollatzResearch.WordTrace]
  refine ⟨232997634335566567472841323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155331756223711044981894215 232997634335566567472841323)
  ·
    refine ⟨349496451503349851209261985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232997634335566567472841323 349496451503349851209261985)
    ·
      refine ⟨262122338627512388406946489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 349496451503349851209261985 262122338627512388406946489)
      ·
        refine ⟨196591753970634291305209867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262122338627512388406946489 196591753970634291305209867)
        ·
          refine ⟨294887630955951436957814801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196591753970634291305209867 294887630955951436957814801)
          ·
            refine ⟨221165723216963577718361101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 294887630955951436957814801 221165723216963577718361101)
            ·
              refine ⟨82937146206361341644385413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 221165723216963577718361101 82937146206361341644385413)
              ·
                refine ⟨15550714913692751558322265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82937146206361341644385413 15550714913692751558322265)
                ·
                  refine ⟨11663036185269563668741699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15550714913692751558322265 11663036185269563668741699)
                  ·
                    refine ⟨17494554277904345503112549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11663036185269563668741699 17494554277904345503112549)
                    ·
                      refine ⟨3280228927107064781833603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17494554277904345503112549 3280228927107064781833603)
                      ·
                        rfl

theorem cell23_6388223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4, 2, 1, 4].length) (baseStart_6388223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6388223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6388223 prefixEnd_6388223 := by exact prefixLift 6388223
  have htrace : WordTrace (prefixWord ++ tailWord_6388223) baseStart_6388223 baseEnd_6388223 := by
    simpa [prefixWord, tailWord_6388223, baseEnd_6388223] using wordTrace_append hprefix tailTrace_6388223
  have hstable : (prefixWord ++ tailWord_6388223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6388223).length < 2 ^ (prefixWord ++ tailWord_6388223).sum := by decide
  have hdescent : baseEnd_6388223 < baseStart_6388223 := by decide
  rcases family_descends (prefixWord ++ tailWord_6388223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6388243 : List Nat := [1, 1, 1, 2, 1, 5, 2, 2, 1, 4, 3]
def baseStart_6388243 : Nat := 118140960795 + 6388243 * 2 ^ 59
def prefixEnd_6388243 : Nat := 4983230072969 + 3 ^ 40 * 6388243 * 2
def baseEnd_6388243 : Nat := 3280239196720154703583511

theorem tailTrace_6388243 : CollatzResearch.WordTrace tailWord_6388243 prefixEnd_6388243 3280239196720154703583511 := by
  unfold tailWord_6388243
  simp only [CollatzResearch.WordTrace]
  refine ⟨232998363795494110888569383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155332242530329407259046255 232998363795494110888569383)
  ·
    refine ⟨349497545693241166332854075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232998363795494110888569383 349497545693241166332854075)
    ·
      refine ⟨524246318539861749499281113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349497545693241166332854075 524246318539861749499281113)
      ·
        refine ⟨393184738904896312124460835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 524246318539861749499281113 393184738904896312124460835)
        ·
          refine ⟨589777108357344468186691253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 393184738904896312124460835 589777108357344468186691253)
          ·
            refine ⟨55291603908501043892502305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 589777108357344468186691253 55291603908501043892502305)
            ·
              refine ⟨41468702931375782919376729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55291603908501043892502305 41468702931375782919376729)
              ·
                refine ⟨31101527198531837189532547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41468702931375782919376729 31101527198531837189532547)
                ·
                  refine ⟨46652290797797755784298821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31101527198531837189532547 46652290797797755784298821)
                  ·
                    refine ⟨8747304524587079209556029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46652290797797755784298821 8747304524587079209556029)
                    ·
                      refine ⟨3280239196720154703583511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8747304524587079209556029 3280239196720154703583511)
                      ·
                        rfl

theorem cell23_6388243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 4, 3].length) (baseStart_6388243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6388243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6388243 prefixEnd_6388243 := by exact prefixLift 6388243
  have htrace : WordTrace (prefixWord ++ tailWord_6388243) baseStart_6388243 baseEnd_6388243 := by
    simpa [prefixWord, tailWord_6388243, baseEnd_6388243] using wordTrace_append hprefix tailTrace_6388243
  have hstable : (prefixWord ++ tailWord_6388243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6388243).length < 2 ^ (prefixWord ++ tailWord_6388243).sum := by decide
  have hdescent : baseEnd_6388243 < baseStart_6388243 := by decide
  rcases family_descends (prefixWord ++ tailWord_6388243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6388300 : List Nat := [2, 2, 1, 3, 1, 2, 1, 1, 3, 5, 2]
def baseStart_6388300 : Nat := 118140960795 + 6388300 * 2 ^ 59
def prefixEnd_6388300 : Nat := 4983230072969 + 3 ^ 40 * 6388300 * 2
def baseEnd_6388300 : Nat := 3280268465117460980570749

theorem tailTrace_6388300 : CollatzResearch.WordTrace tailWord_6388300 prefixEnd_6388300 3280268465117460980570749 := by
  unfold tailWord_6388300
  simp only [CollatzResearch.WordTrace]
  refine ⟨116500221378143804811697177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155333628504191739748929569 116500221378143804811697177)
  ·
    refine ⟨87375166033607853608772883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116500221378143804811697177 87375166033607853608772883)
    ·
      refine ⟨131062749050411780413159325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87375166033607853608772883 131062749050411780413159325)
      ·
        refine ⟨49148530893904417654934747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131062749050411780413159325 49148530893904417654934747)
        ·
          refine ⟨73722796340856626482402121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49148530893904417654934747 73722796340856626482402121)
          ·
            refine ⟨55292097255642469861801591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73722796340856626482402121 55292097255642469861801591)
            ·
              refine ⟨82938145883463704792702387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55292097255642469861801591 82938145883463704792702387)
              ·
                refine ⟨124407218825195557189053581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82938145883463704792702387 124407218825195557189053581)
                ·
                  refine ⟨46652707059448333945895093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 124407218825195557189053581 46652707059448333945895093)
                  ·
                    refine ⟨4373691286823281307427665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46652707059448333945895093 4373691286823281307427665)
                    ·
                      refine ⟨3280268465117460980570749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4373691286823281307427665 3280268465117460980570749)
                      ·
                        rfl

theorem cell23_6388300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 3, 5, 2].length) (baseStart_6388300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6388300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6388300 prefixEnd_6388300 := by exact prefixLift 6388300
  have htrace : WordTrace (prefixWord ++ tailWord_6388300) baseStart_6388300 baseEnd_6388300 := by
    simpa [prefixWord, tailWord_6388300, baseEnd_6388300] using wordTrace_append hprefix tailTrace_6388300
  have hstable : (prefixWord ++ tailWord_6388300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6388300).length < 2 ^ (prefixWord ++ tailWord_6388300).sum := by decide
  have hdescent : baseEnd_6388300 < baseStart_6388300 := by decide
  rcases family_descends (prefixWord ++ tailWord_6388300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6388323 : List Nat := [1, 1, 1, 5, 1, 2, 2, 1, 3, 6]
def baseStart_6388323 : Nat := 118140960795 + 6388323 * 2 ^ 59
def prefixEnd_6388323 : Nat := 4983230072969 + 3 ^ 40 * 6388323 * 2
def baseEnd_6388323 : Nat := 1093426758390838130194381

theorem tailTrace_6388323 : CollatzResearch.WordTrace tailWord_6388323 prefixEnd_6388323 1093426758390838130194381 := by
  unfold tailWord_6388323
  simp only [CollatzResearch.WordTrace]
  refine ⟨233001281635204284551481623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155334187756802856367654415 233001281635204284551481623)
  ·
    refine ⟨349501922452806426827222435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233001281635204284551481623 349501922452806426827222435)
    ·
      refine ⟨524252883679209640240833653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349501922452806426827222435 524252883679209640240833653)
      ·
        refine ⟨49148707844925903772578155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 524252883679209640240833653 49148707844925903772578155)
        ·
          refine ⟨73723061767388855658867233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49148707844925903772578155 73723061767388855658867233)
          ·
            refine ⟨55292296325541641744150425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73723061767388855658867233 55292296325541641744150425)
            ·
              refine ⟨41469222244156231308112819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55292296325541641744150425 41469222244156231308112819)
              ·
                refine ⟨62203833366234346962169229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41469222244156231308112819 62203833366234346962169229)
                ·
                  refine ⟨23326437512337880110813461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62203833366234346962169229 23326437512337880110813461)
                  ·
                    refine ⟨1093426758390838130194381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23326437512337880110813461 1093426758390838130194381)
                    ·
                      rfl

theorem cell23_6388323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 3, 6].length) (baseStart_6388323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6388323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6388323 prefixEnd_6388323 := by exact prefixLift 6388323
  have htrace : WordTrace (prefixWord ++ tailWord_6388323) baseStart_6388323 baseEnd_6388323 := by
    simpa [prefixWord, tailWord_6388323, baseEnd_6388323] using wordTrace_append hprefix tailTrace_6388323
  have hstable : (prefixWord ++ tailWord_6388323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6388323).length < 2 ^ (prefixWord ++ tailWord_6388323).sum := by decide
  have hdescent : baseEnd_6388323 < baseStart_6388323 := by decide
  rcases family_descends (prefixWord ++ tailWord_6388323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6388334 : List Nat := [4, 1, 2, 2, 2, 2, 1, 2, 2, 3, 2]
def baseStart_6388334 : Nat := 118140960795 + 6388334 * 2 ^ 59
def prefixEnd_6388334 : Nat := 4983230072969 + 3 ^ 40 * 6388334 * 2
def baseEnd_6388334 : Nat := 3280285923459713847545593

theorem tailTrace_6388334 : CollatzResearch.WordTrace tailWord_6388334 prefixEnd_6388334 3280285923459713847545593 := by
  unfold tailWord_6388334
  simp only [CollatzResearch.WordTrace]
  refine ⟨29125210354770554178766507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155334455225442955620088037 29125210354770554178766507)
  ·
    refine ⟨43687815532155831268149761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29125210354770554178766507 43687815532155831268149761)
    ·
      refine ⟨32765861649116873451112321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43687815532155831268149761 32765861649116873451112321)
      ·
        refine ⟨24574396236837655088334241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32765861649116873451112321 24574396236837655088334241)
        ·
          refine ⟨18430797177628241316250681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24574396236837655088334241 18430797177628241316250681)
          ·
            refine ⟨13823097883221180987188011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18430797177628241316250681 13823097883221180987188011)
            ·
              refine ⟨20734646824831771480782017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13823097883221180987188011 20734646824831771480782017)
              ·
                refine ⟨15550985118623828610586513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20734646824831771480782017 15550985118623828610586513)
                ·
                  refine ⟨11663238838967871457939885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15550985118623828610586513 11663238838967871457939885)
                  ·
                    refine ⟨4373714564612951796727457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11663238838967871457939885 4373714564612951796727457)
                    ·
                      refine ⟨3280285923459713847545593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4373714564612951796727457 3280285923459713847545593)
                      ·
                        rfl

theorem cell23_6388334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_6388334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6388334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6388334 prefixEnd_6388334 := by exact prefixLift 6388334
  have htrace : WordTrace (prefixWord ++ tailWord_6388334) baseStart_6388334 baseEnd_6388334 := by
    simpa [prefixWord, tailWord_6388334, baseEnd_6388334] using wordTrace_append hprefix tailTrace_6388334
  have hstable : (prefixWord ++ tailWord_6388334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6388334).length < 2 ^ (prefixWord ++ tailWord_6388334).sum := by decide
  have hdescent : baseEnd_6388334 < baseStart_6388334 := by decide
  rcases family_descends (prefixWord ++ tailWord_6388334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6388341 : List Nat := [1, 3, 4, 2, 2, 2, 1, 1, 3, 1, 3]
def baseStart_6388341 : Nat := 118140960795 + 6388341 * 2 ^ 59
def prefixEnd_6388341 : Nat := 4983230072969 + 3 ^ 40 * 6388341 * 2
def baseEnd_6388341 : Nat := 3280289517824295320158061

theorem tailTrace_6388341 : CollatzResearch.WordTrace tailWord_6388341 prefixEnd_6388341 3280289517824295320158061 := by
  unfold tailWord_6388341
  simp only [CollatzResearch.WordTrace]
  refine ⟨233001938149139073625636877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155334625432759382417091251 233001938149139073625636877)
  ·
    refine ⟨87375726805927152609613829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233001938149139073625636877 87375726805927152609613829)
    ·
      refine ⟨16382948776111341114302593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87375726805927152609613829 16382948776111341114302593)
      ·
        refine ⟨12287211582083505835726945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16382948776111341114302593 12287211582083505835726945)
        ·
          refine ⟨9215408686562629376795209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12287211582083505835726945 9215408686562629376795209)
          ·
            refine ⟨6911556514921972032596407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9215408686562629376795209 6911556514921972032596407)
            ·
              refine ⟨10367334772382958048894611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6911556514921972032596407 10367334772382958048894611)
              ·
                refine ⟨15551002158574437073341917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10367334772382958048894611 15551002158574437073341917)
                ·
                  refine ⟨5831625809465413902503219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15551002158574437073341917 5831625809465413902503219)
                  ·
                    refine ⟨8747438714198120853754829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5831625809465413902503219 8747438714198120853754829)
                    ·
                      refine ⟨3280289517824295320158061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8747438714198120853754829 3280289517824295320158061)
                      ·
                        rfl

theorem cell23_6388341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_6388341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6388341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6388341 prefixEnd_6388341 := by exact prefixLift 6388341
  have htrace : WordTrace (prefixWord ++ tailWord_6388341) baseStart_6388341 baseEnd_6388341 := by
    simpa [prefixWord, tailWord_6388341, baseEnd_6388341] using wordTrace_append hprefix tailTrace_6388341
  have hstable : (prefixWord ++ tailWord_6388341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6388341).length < 2 ^ (prefixWord ++ tailWord_6388341).sum := by decide
  have hdescent : baseEnd_6388341 < baseStart_6388341 := by decide
  rcases family_descends (prefixWord ++ tailWord_6388341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6388343 : List Nat := [1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 6]
def baseStart_6388343 : Nat := 118140960795 + 6388343 * 2 ^ 59
def prefixEnd_6388343 : Nat := 4983230072969 + 3 ^ 40 * 6388343 * 2
def baseEnd_6388343 : Nat := 3280290544785604312333051

theorem tailTrace_6388343 : CollatzResearch.WordTrace tailWord_6388343 prefixEnd_6388343 3280290544785604312333051 := by
  unfold tailWord_6388343
  simp only [CollatzResearch.WordTrace]
  refine ⟨233002011095131827967209683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155334674063421218644806455 233002011095131827967209683)
  ·
    refine ⟨349503016642697741950814525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233002011095131827967209683 349503016642697741950814525)
    ·
      refine ⟨131063631241011653231555447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 349503016642697741950814525 131063631241011653231555447)
      ·
        refine ⟨196595446861517479847333171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131063631241011653231555447 196595446861517479847333171)
        ·
          refine ⟨294893170292276219770999757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196595446861517479847333171 294893170292276219770999757)
          ·
            refine ⟨110584938859603582414124909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 294893170292276219770999757 110584938859603582414124909)
            ·
              refine ⟨41469352072351343405296841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110584938859603582414124909 41469352072351343405296841)
              ·
                refine ⟨31102014054263507553972631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41469352072351343405296841 31102014054263507553972631)
                ·
                  refine ⟨46653021081395261330958947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31102014054263507553972631 46653021081395261330958947)
                  ·
                    refine ⟨69979531622092891996438421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46653021081395261330958947 69979531622092891996438421)
                    ·
                      refine ⟨3280290544785604312333051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69979531622092891996438421 3280290544785604312333051)
                      ·
                        rfl

theorem cell23_6388343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 6].length) (baseStart_6388343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6388343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6388343 prefixEnd_6388343 := by exact prefixLift 6388343
  have htrace : WordTrace (prefixWord ++ tailWord_6388343) baseStart_6388343 baseEnd_6388343 := by
    simpa [prefixWord, tailWord_6388343, baseEnd_6388343] using wordTrace_append hprefix tailTrace_6388343
  have hstable : (prefixWord ++ tailWord_6388343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6388343).length < 2 ^ (prefixWord ++ tailWord_6388343).sum := by decide
  have hdescent : baseEnd_6388343 < baseStart_6388343 := by decide
  rcases family_descends (prefixWord ++ tailWord_6388343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6388347 : List Nat := [1, 1, 1, 1, 1, 4, 2, 5, 3, 2, 2]
def baseStart_6388347 : Nat := 118140960795 + 6388347 * 2 ^ 59
def prefixEnd_6388347 : Nat := 4983230072969 + 3 ^ 40 * 6388347 * 2
def baseEnd_6388347 : Nat := 3280292598708222296683033

theorem tailTrace_6388347 : CollatzResearch.WordTrace tailWord_6388347 prefixEnd_6388347 3280292598708222296683033 := by
  unfold tailWord_6388347
  simp only [CollatzResearch.WordTrace]
  refine ⟨233002156987117336650355295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155334771324744891100236863 233002156987117336650355295)
  ·
    refine ⟨349503235480676004975532943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233002156987117336650355295 349503235480676004975532943)
    ·
      refine ⟨524254853221014007463299415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349503235480676004975532943 524254853221014007463299415)
      ·
        refine ⟨786382279831521011194949123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 524254853221014007463299415 786382279831521011194949123)
        ·
          refine ⟨1179573419747281516792423685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 786382279831521011194949123 1179573419747281516792423685)
          ·
            refine ⟨221170016202615284398579441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1179573419747281516792423685 221170016202615284398579441)
            ·
              refine ⟨165877512151961463298934581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221170016202615284398579441 165877512151961463298934581)
              ·
                refine ⟨15551016764246387184275117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 165877512151961463298934581 15551016764246387184275117)
                ·
                  refine ⟨5831631286592395194103169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15551016764246387184275117 5831631286592395194103169)
                  ·
                    refine ⟨4373723464944296395577377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5831631286592395194103169 4373723464944296395577377)
                    ·
                      refine ⟨3280292598708222296683033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4373723464944296395577377 3280292598708222296683033)
                      ·
                        rfl

theorem cell23_6388347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5, 3, 2, 2].length) (baseStart_6388347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6388347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6388347 prefixEnd_6388347 := by exact prefixLift 6388347
  have htrace : WordTrace (prefixWord ++ tailWord_6388347) baseStart_6388347 baseEnd_6388347 := by
    simpa [prefixWord, tailWord_6388347, baseEnd_6388347] using wordTrace_append hprefix tailTrace_6388347
  have hstable : (prefixWord ++ tailWord_6388347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6388347).length < 2 ^ (prefixWord ++ tailWord_6388347).sum := by decide
  have hdescent : baseEnd_6388347 < baseStart_6388347 := by decide
  rcases family_descends (prefixWord ++ tailWord_6388347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6388357 : List Nat := [1, 3, 1, 1, 4, 3, 1, 3, 2, 4]
def baseStart_6388357 : Nat := 118140960795 + 6388357 * 2 ^ 59
def prefixEnd_6388357 : Nat := 4983230072969 + 3 ^ 40 * 6388357 * 2
def baseEnd_6388357 : Nat := 1093432577838255752519329

theorem tailTrace_6388357 : CollatzResearch.WordTrace tailWord_6388357 prefixEnd_6388357 1093432577838255752519329 := by
  unfold tailWord_6388357
  simp only [CollatzResearch.WordTrace]
  refine ⟨233002521717081108358219325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155335014478054072238812883 233002521717081108358219325)
  ·
    refine ⟨87375945643905415634332247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233002521717081108358219325 87375945643905415634332247)
    ·
      refine ⟨131063918465858123451498371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87375945643905415634332247 131063918465858123451498371)
      ·
        refine ⟨196595877698787185177247557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131063918465858123451498371 196595877698787185177247557)
        ·
          refine ⟨36861727068522597220733917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 196595877698787185177247557 36861727068522597220733917)
          ·
            refine ⟨13823147650695973957775219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36861727068522597220733917 13823147650695973957775219)
            ·
              refine ⟨20734721476043960936662829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13823147650695973957775219 20734721476043960936662829)
              ·
                refine ⟨7775520553516485351248561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20734721476043960936662829 7775520553516485351248561)
                ·
                  refine ⟨5831640415137364013436421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7775520553516485351248561 5831640415137364013436421)
                  ·
                    refine ⟨1093432577838255752519329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5831640415137364013436421 1093432577838255752519329)
                    ·
                      rfl

theorem cell23_6388357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 3, 2, 4].length) (baseStart_6388357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6388357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6388357 prefixEnd_6388357 := by exact prefixLift 6388357
  have htrace : WordTrace (prefixWord ++ tailWord_6388357) baseStart_6388357 baseEnd_6388357 := by
    simpa [prefixWord, tailWord_6388357, baseEnd_6388357] using wordTrace_append hprefix tailTrace_6388357
  have hstable : (prefixWord ++ tailWord_6388357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6388357).length < 2 ^ (prefixWord ++ tailWord_6388357).sum := by decide
  have hdescent : baseEnd_6388357 < baseStart_6388357 := by decide
  rcases family_descends (prefixWord ++ tailWord_6388357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6388370 : List Nat := [3, 2, 3, 1, 2, 1, 2, 9]
def baseStart_6388370 : Nat := 118140960795 + 6388370 * 2 ^ 59
def prefixEnd_6388370 : Nat := 4983230072969 + 3 ^ 40 * 6388370 * 2
def baseEnd_6388370 : Nat := 121492755880121322470201

theorem tailTrace_6388370 : CollatzResearch.WordTrace tailWord_6388370 prefixEnd_6388370 121492755880121322470201 := by
  unfold tailWord_6388370
  simp only [CollatzResearch.WordTrace]
  refine ⟨58250748966508502894610641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155335330577356007718961709 58250748966508502894610641)
  ·
    refine ⟨43688061724881377170957981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58250748966508502894610641 43688061724881377170957981)
    ·
      refine ⟨16383023146830516439109243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43688061724881377170957981 16383023146830516439109243)
      ·
        refine ⟨24574534720245774658663865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16383023146830516439109243 24574534720245774658663865)
        ·
          refine ⟨18430901040184330993997899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24574534720245774658663865 18430901040184330993997899)
          ·
            refine ⟨27646351560276496490996849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18430901040184330993997899 27646351560276496490996849)
            ·
              refine ⟨20734763670207372368247637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27646351560276496490996849 20734763670207372368247637)
              ·
                refine ⟨121492755880121322470201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20734763670207372368247637 121492755880121322470201)
                ·
                  rfl

theorem cell23_6388370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 9].length) (baseStart_6388370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6388370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6388370 prefixEnd_6388370 := by exact prefixLift 6388370
  have htrace : WordTrace (prefixWord ++ tailWord_6388370) baseStart_6388370 baseEnd_6388370 := by
    simpa [prefixWord, tailWord_6388370, baseEnd_6388370] using wordTrace_append hprefix tailTrace_6388370
  have hstable : (prefixWord ++ tailWord_6388370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6388370).length < 2 ^ (prefixWord ++ tailWord_6388370).sum := by decide
  have hdescent : baseEnd_6388370 < baseStart_6388370 := by decide
  rcases family_descends (prefixWord ++ tailWord_6388370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6388384 : List Nat := [2, 1, 1, 4, 5, 1, 1, 1, 1, 1, 5]
def baseStart_6388384 : Nat := 118140960795 + 6388384 * 2 ^ 59
def prefixEnd_6388384 : Nat := 4983230072969 + 3 ^ 40 * 6388384 * 2
def baseEnd_6388384 : Nat := 3280311597492438651920363

theorem tailTrace_6388384 : CollatzResearch.WordTrace tailWord_6388384 prefixEnd_6388384 3280311597492438651920363 := by
  unfold tailWord_6388384
  simp only [CollatzResearch.WordTrace]
  refine ⟨116501753243991645984726103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155335670991988861312968137 116501753243991645984726103)
  ·
    refine ⟨174752629865987468977089155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116501753243991645984726103 174752629865987468977089155)
    ·
      refine ⟨262128944798981203465633733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174752629865987468977089155 262128944798981203465633733)
      ·
        refine ⟨49149177149808975649806325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 262128944798981203465633733 49149177149808975649806325)
        ·
          refine ⟨4607735357794591467169343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49149177149808975649806325 4607735357794591467169343)
          ·
            refine ⟨6911603036691887200754015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4607735357794591467169343 6911603036691887200754015)
            ·
              refine ⟨10367404555037830801131023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6911603036691887200754015 10367404555037830801131023)
              ·
                refine ⟨15551106832556746201696535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10367404555037830801131023 15551106832556746201696535)
                ·
                  refine ⟨23326660248835119302544803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15551106832556746201696535 23326660248835119302544803)
                  ·
                    refine ⟨34989990373252678953817205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23326660248835119302544803 34989990373252678953817205)
                    ·
                      refine ⟨3280311597492438651920363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34989990373252678953817205 3280311597492438651920363)
                      ·
                        rfl

theorem cell23_6388384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 1, 1, 1, 5].length) (baseStart_6388384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6388384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6388384 prefixEnd_6388384 := by exact prefixLift 6388384
  have htrace : WordTrace (prefixWord ++ tailWord_6388384) baseStart_6388384 baseEnd_6388384 := by
    simpa [prefixWord, tailWord_6388384, baseEnd_6388384] using wordTrace_append hprefix tailTrace_6388384
  have hstable : (prefixWord ++ tailWord_6388384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6388384).length < 2 ^ (prefixWord ++ tailWord_6388384).sum := by decide
  have hdescent : baseEnd_6388384 < baseStart_6388384 := by decide
  rcases family_descends (prefixWord ++ tailWord_6388384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6388391 : List Nat := [1, 1, 6, 3, 1, 1, 2, 2, 2, 4]
def baseStart_6388391 : Nat := 118140960795 + 6388391 * 2 ^ 59
def prefixEnd_6388391 : Nat := 4983230072969 + 3 ^ 40 * 6388391 * 2
def baseEnd_6388391 : Nat := 1093438397285673374844277

theorem tailTrace_6388391 : CollatzResearch.WordTrace tailWord_6388391 prefixEnd_6388391 1093438397285673374844277 := by
  unfold tailWord_6388391
  simp only [CollatzResearch.WordTrace]
  refine ⟨233003761798957932164957027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155335841199305288109971351 233003761798957932164957027)
  ·
    refine ⟨349505642698436898247435541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233003761798957932164957027 349505642698436898247435541)
    ·
      refine ⟨16383077001489229605348541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 349505642698436898247435541 16383077001489229605348541)
      ·
        refine ⟨6143653875558461102005703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16383077001489229605348541 6143653875558461102005703)
        ·
          refine ⟨9215480813337691653008555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6143653875558461102005703 9215480813337691653008555)
          ·
            refine ⟨13823221220006537479512833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9215480813337691653008555 13823221220006537479512833)
            ·
              refine ⟨10367415915004903109634625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13823221220006537479512833 10367415915004903109634625)
              ·
                refine ⟨7775561936253677332225969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10367415915004903109634625 7775561936253677332225969)
                ·
                  refine ⟨5831671452190257999169477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7775561936253677332225969 5831671452190257999169477)
                  ·
                    refine ⟨1093438397285673374844277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5831671452190257999169477 1093438397285673374844277)
                    ·
                      rfl

theorem cell23_6388391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_6388391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6388391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6388391 prefixEnd_6388391 := by exact prefixLift 6388391
  have htrace : WordTrace (prefixWord ++ tailWord_6388391) baseStart_6388391 baseEnd_6388391 := by
    simpa [prefixWord, tailWord_6388391, baseEnd_6388391] using wordTrace_append hprefix tailTrace_6388391
  have hstable : (prefixWord ++ tailWord_6388391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6388391).length < 2 ^ (prefixWord ++ tailWord_6388391).sum := by decide
  have hdescent : baseEnd_6388391 < baseStart_6388391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6388391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6388393 : List Nat := [1, 2, 1, 1, 1, 1, 2, 3, 4, 2, 5]
def baseStart_6388393 : Nat := 118140960795 + 6388393 * 2 ^ 59
def prefixEnd_6388393 : Nat := 4983230072969 + 3 ^ 40 * 6388393 * 2
def baseEnd_6388393 : Nat := 3280316218818329116707821

theorem tailTrace_6388393 : CollatzResearch.WordTrace tailWord_6388393 prefixEnd_6388393 3280316218818329116707821 := by
  unfold tailWord_6388393
  simp only [CollatzResearch.WordTrace]
  refine ⟨233003834744950686506529833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155335889829967124337686555 233003834744950686506529833)
  ·
    refine ⟨174752876058713014879897375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233003834744950686506529833 174752876058713014879897375)
    ·
      refine ⟨262129314088069522319846063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174752876058713014879897375 262129314088069522319846063)
      ·
        refine ⟨393193971132104283479769095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262129314088069522319846063 393193971132104283479769095)
        ·
          refine ⟨589790956698156425219653643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 393193971132104283479769095 589790956698156425219653643)
          ·
            refine ⟨884686435047234637829480465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 589790956698156425219653643 884686435047234637829480465)
            ·
              refine ⟨663514826285425978372110349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 884686435047234637829480465 663514826285425978372110349)
              ·
                refine ⟨248818059857034741889541381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 663514826285425978372110349 248818059857034741889541381)
                ·
                  refine ⟨46653386223194014104289009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 248818059857034741889541381 46653386223194014104289009)
                  ·
                    refine ⟨34990039667395510578216757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46653386223194014104289009 34990039667395510578216757)
                    ·
                      refine ⟨3280316218818329116707821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34990039667395510578216757 3280316218818329116707821)
                      ·
                        rfl

theorem cell23_6388393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 2, 5].length) (baseStart_6388393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6388393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6388393 prefixEnd_6388393 := by exact prefixLift 6388393
  have htrace : WordTrace (prefixWord ++ tailWord_6388393) baseStart_6388393 baseEnd_6388393 := by
    simpa [prefixWord, tailWord_6388393, baseEnd_6388393] using wordTrace_append hprefix tailTrace_6388393
  have hstable : (prefixWord ++ tailWord_6388393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6388393).length < 2 ^ (prefixWord ++ tailWord_6388393).sum := by decide
  have hdescent : baseEnd_6388393 < baseStart_6388393 := by decide
  rcases family_descends (prefixWord ++ tailWord_6388393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6388414 : List Nat := [4, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3]
def baseStart_6388414 : Nat := 118140960795 + 6388414 * 2 ^ 59
def prefixEnd_6388414 : Nat := 4983230072969 + 3 ^ 40 * 6388414 * 2
def baseEnd_6388414 : Nat := 3280327001912073534545225

theorem tailTrace_6388414 : CollatzResearch.WordTrace tailWord_6388414 prefixEnd_6388414 3280327001912073534545225 := by
  unfold tailWord_6388414
  simp only [CollatzResearch.WordTrace]
  refine ⟨29125575084734325886630537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155336400451916404728696197 29125575084734325886630537)
  ·
    refine ⟨21844181313550744414972903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29125575084734325886630537 21844181313550744414972903)
    ·
      refine ⟨32766271970326116622459355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21844181313550744414972903 32766271970326116622459355)
      ·
        refine ⟨49149407955489174933689033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32766271970326116622459355 49149407955489174933689033)
        ·
          refine ⟨36862055966616881200266775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49149407955489174933689033 36862055966616881200266775)
          ·
            refine ⟨55293083949925321800400163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36862055966616881200266775 55293083949925321800400163)
            ·
              refine ⟨82939625924887982700600245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55293083949925321800400163 82939625924887982700600245)
              ·
                refine ⟨7775589930458248378181273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82939625924887982700600245 7775589930458248378181273)
                ·
                  refine ⟨5831692447843686283635955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7775589930458248378181273 5831692447843686283635955)
                  ·
                    refine ⟨8747538671765529425453933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5831692447843686283635955 8747538671765529425453933)
                    ·
                      refine ⟨3280327001912073534545225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8747538671765529425453933 3280327001912073534545225)
                      ·
                        rfl

theorem cell23_6388414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3].length) (baseStart_6388414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6388414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6388414 prefixEnd_6388414 := by exact prefixLift 6388414
  have htrace : WordTrace (prefixWord ++ tailWord_6388414) baseStart_6388414 baseEnd_6388414 := by
    simpa [prefixWord, tailWord_6388414, baseEnd_6388414] using wordTrace_append hprefix tailTrace_6388414
  have hstable : (prefixWord ++ tailWord_6388414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6388414).length < 2 ^ (prefixWord ++ tailWord_6388414).sum := by decide
  have hdescent : baseEnd_6388414 < baseStart_6388414 := by decide
  rcases family_descends (prefixWord ++ tailWord_6388414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6388490 : List Nat := [3, 1, 2, 2, 1, 2, 1, 3, 1, 7]
def baseStart_6388490 : Nat := 118140960795 + 6388490 * 2 ^ 59
def prefixEnd_6388490 : Nat := 4983230072969 + 3 ^ 40 * 6388490 * 2
def baseEnd_6388490 : Nat := 1093455342147271745731625

theorem tailTrace_6388490 : CollatzResearch.WordTrace tailWord_6388490 prefixEnd_6388490 1093455342147271745731625 := by
  unfold tailWord_6388490
  simp only [CollatzResearch.WordTrace]
  refine ⟨58251843156399818018202731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155338248417066181381873949 58251843156399818018202731)
  ·
    refine ⟨87377764734599727027304097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58251843156399818018202731 87377764734599727027304097)
    ·
      refine ⟨65533323550949795270478073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87377764734599727027304097 65533323550949795270478073)
      ·
        refine ⟨49149992663212346452858555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65533323550949795270478073 49149992663212346452858555)
        ·
          refine ⟨73724988994818519679287833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49149992663212346452858555 73724988994818519679287833)
          ·
            refine ⟨55293741746113889759465875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73724988994818519679287833 55293741746113889759465875)
            ·
              refine ⟨82940612619170834639198813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55293741746113889759465875 82940612619170834639198813)
              ·
                refine ⟨31102729732189062989699555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82940612619170834639198813 31102729732189062989699555)
                ·
                  refine ⟨46654094598283594484549333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31102729732189062989699555 46654094598283594484549333)
                  ·
                    refine ⟨1093455342147271745731625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46654094598283594484549333 1093455342147271745731625)
                    ·
                      rfl

theorem cell23_6388490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 1, 7].length) (baseStart_6388490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6388490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6388490 prefixEnd_6388490 := by exact prefixLift 6388490
  have htrace : WordTrace (prefixWord ++ tailWord_6388490) baseStart_6388490 baseEnd_6388490 := by
    simpa [prefixWord, tailWord_6388490, baseEnd_6388490] using wordTrace_append hprefix tailTrace_6388490
  have hstable : (prefixWord ++ tailWord_6388490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6388490).length < 2 ^ (prefixWord ++ tailWord_6388490).sum := by decide
  have hdescent : baseEnd_6388490 < baseStart_6388490 := by decide
  rcases family_descends (prefixWord ++ tailWord_6388490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6388522 : List Nat := [3, 1, 4, 3, 1, 2, 2, 1, 2, 2, 2]
def baseStart_6388522 : Nat := 118140960795 + 6388522 * 2 ^ 59
def prefixEnd_6388522 : Nat := 4983230072969 + 3 ^ 40 * 6388522 * 2
def baseEnd_6388522 : Nat := 3280382457822759111994729

theorem tailTrace_6388522 : CollatzResearch.WordTrace tailWord_6388522 prefixEnd_6388522 3280382457822759111994729 := by
  unfold tailWord_6388522
  simp only [CollatzResearch.WordTrace]
  refine ⟨58252134940370835384493955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155339026507655561025317213 58252134940370835384493955)
  ·
    refine ⟨87378202410556253076740933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58252134940370835384493955 87378202410556253076740933)
    ·
      refine ⟨16383412951979297451888925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87378202410556253076740933 16383412951979297451888925)
      ·
        refine ⟨6143779856992236544458347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16383412951979297451888925 6143779856992236544458347)
        ·
          refine ⟨9215669785488354816687521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6143779856992236544458347 9215669785488354816687521)
          ·
            refine ⟨6911752339116266112515641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9215669785488354816687521 6911752339116266112515641)
            ·
              refine ⟨5183814254337199584386731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6911752339116266112515641 5183814254337199584386731)
              ·
                refine ⟨7775721381505799376580097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5183814254337199584386731 7775721381505799376580097)
                ·
                  refine ⟨5831791036129349532435073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7775721381505799376580097 5831791036129349532435073)
                  ·
                    refine ⟨4373843277097012149326305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5831791036129349532435073 4373843277097012149326305)
                    ·
                      refine ⟨3280382457822759111994729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4373843277097012149326305 3280382457822759111994729)
                      ·
                        rfl

theorem cell23_6388522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_6388522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6388522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6388522 prefixEnd_6388522 := by exact prefixLift 6388522
  have htrace : WordTrace (prefixWord ++ tailWord_6388522) baseStart_6388522 baseEnd_6388522 := by
    simpa [prefixWord, tailWord_6388522, baseEnd_6388522] using wordTrace_append hprefix tailTrace_6388522
  have hstable : (prefixWord ++ tailWord_6388522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6388522).length < 2 ^ (prefixWord ++ tailWord_6388522).sum := by decide
  have hdescent : baseEnd_6388522 < baseStart_6388522 := by decide
  rcases family_descends (prefixWord ++ tailWord_6388522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6388540 : List Nat := [2, 2, 2, 2, 1, 1, 1, 2, 1, 3, 6]
def baseStart_6388540 : Nat := 118140960795 + 6388540 * 2 ^ 59
def prefixEnd_6388540 : Nat := 4983230072969 + 3 ^ 40 * 6388540 * 2
def baseEnd_6388540 : Nat := 3280391700474540041569645

theorem tailTrace_6388540 : CollatzResearch.WordTrace tailWord_6388540 prefixEnd_6388540 3280391700474540041569645 := by
  unfold tailWord_6388540
  simp only [CollatzResearch.WordTrace]
  refine ⟨116504598137709065306065537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155339464183612087074754049 116504598137709065306065537)
  ·
    refine ⟨87378448603281798979549153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116504598137709065306065537 87378448603281798979549153)
    ·
      refine ⟨65533836452461349234661865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87378448603281798979549153 65533836452461349234661865)
      ·
        refine ⟨49150377339346011925996399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65533836452461349234661865 49150377339346011925996399)
        ·
          refine ⟨73725566009019017888994599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49150377339346011925996399 73725566009019017888994599)
          ·
            refine ⟨110588349013528526833491899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73725566009019017888994599 110588349013528526833491899)
            ·
              refine ⟨165882523520292790250237849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110588349013528526833491899 165882523520292790250237849)
              ·
                refine ⟨124411892640219592687678387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165882523520292790250237849 124411892640219592687678387)
                ·
                  refine ⟨186617838960329389031517581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124411892640219592687678387 186617838960329389031517581)
                  ·
                    refine ⟨69981689610123520886819093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 186617838960329389031517581 69981689610123520886819093)
                    ·
                      refine ⟨3280391700474540041569645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69981689610123520886819093 3280391700474540041569645)
                      ·
                        rfl

theorem cell23_6388540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_6388540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6388540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6388540 prefixEnd_6388540 := by exact prefixLift 6388540
  have htrace : WordTrace (prefixWord ++ tailWord_6388540) baseStart_6388540 baseEnd_6388540 := by
    simpa [prefixWord, tailWord_6388540, baseEnd_6388540] using wordTrace_append hprefix tailTrace_6388540
  have hstable : (prefixWord ++ tailWord_6388540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6388540).length < 2 ^ (prefixWord ++ tailWord_6388540).sum := by decide
  have hdescent : baseEnd_6388540 < baseStart_6388540 := by decide
  rcases family_descends (prefixWord ++ tailWord_6388540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6388567 : List Nat := [1, 1, 3, 2, 4, 1, 1, 4, 6]
def baseStart_6388567 : Nat := 118140960795 + 6388567 * 2 ^ 59
def prefixEnd_6388567 : Nat := 4983230072969 + 3 ^ 40 * 6388567 * 2
def baseEnd_6388567 : Nat := 364489507161356826214669

theorem tailTrace_6388567 : CollatzResearch.WordTrace tailWord_6388567 prefixEnd_6388567 364489507161356826214669 := by
  unfold tailWord_6388567
  simp only [CollatzResearch.WordTrace]
  refine ⟨233010181046320314223363955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155340120697546876148909303 233010181046320314223363955)
  ·
    refine ⟨349515271569480471335045933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233010181046320314223363955 349515271569480471335045933)
    ·
      refine ⟨131068226838555176750642225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 349515271569480471335045933 131068226838555176750642225)
      ·
        refine ⟨98301170128916382562981669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131068226838555176750642225 98301170128916382562981669)
        ·
          refine ⟨18431469399171821730559063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98301170128916382562981669 18431469399171821730559063)
          ·
            refine ⟨27647204098757732595838595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18431469399171821730559063 27647204098757732595838595)
            ·
              refine ⟨41470806148136598893757893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27647204098757732595838595 41470806148136598893757893)
              ·
                refine ⟨7775776152775612292579605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41470806148136598893757893 7775776152775612292579605)
                ·
                  refine ⟨364489507161356826214669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7775776152775612292579605 364489507161356826214669)
                  ·
                    rfl

theorem cell23_6388567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 4, 6].length) (baseStart_6388567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6388567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6388567 prefixEnd_6388567 := by exact prefixLift 6388567
  have htrace : WordTrace (prefixWord ++ tailWord_6388567) baseStart_6388567 baseEnd_6388567 := by
    simpa [prefixWord, tailWord_6388567, baseEnd_6388567] using wordTrace_append hprefix tailTrace_6388567
  have hstable : (prefixWord ++ tailWord_6388567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6388567).length < 2 ^ (prefixWord ++ tailWord_6388567).sum := by decide
  have hdescent : baseEnd_6388567 < baseStart_6388567 := by decide
  rcases family_descends (prefixWord ++ tailWord_6388567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6388594 : List Nat := [3, 2, 1, 2, 1, 1, 3, 1, 5, 1, 3]
def baseStart_6388594 : Nat := 118140960795 + 6388594 * 2 ^ 59
def prefixEnd_6388594 : Nat := 4983230072969 + 3 ^ 40 * 6388594 * 2
def baseEnd_6388594 : Nat := 3280419428429882830294397

theorem tailTrace_6388594 : CollatzResearch.WordTrace tailWord_6388594 prefixEnd_6388594 3280419428429882830294397 := by
  unfold tailWord_6388594
  simp only [CollatzResearch.WordTrace]
  refine ⟨58252791454305624458649209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155340777211481665223064557 58252791454305624458649209)
  ·
    refine ⟨43689593590729218343986907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58252791454305624458649209 43689593590729218343986907)
    ·
      refine ⟨65534390386093827515980361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43689593590729218343986907 65534390386093827515980361)
      ·
        refine ⟨49150792789570370636985271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65534390386093827515980361 49150792789570370636985271)
        ·
          refine ⟨73726189184355555955477907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49150792789570370636985271 73726189184355555955477907)
          ·
            refine ⟨110589283776533333933216861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73726189184355555955477907 110589283776533333933216861)
            ·
              refine ⟨41470981416200000224956323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110589283776533333933216861 41470981416200000224956323)
              ·
                refine ⟨62206472124300000337434485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41470981416200000224956323 62206472124300000337434485)
                ·
                  refine ⟨5831856761653125031634483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62206472124300000337434485 5831856761653125031634483)
                  ·
                    refine ⟨8747785142479687547451725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5831856761653125031634483 8747785142479687547451725)
                    ·
                      refine ⟨3280419428429882830294397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8747785142479687547451725 3280419428429882830294397)
                      ·
                        rfl

theorem cell23_6388594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 5, 1, 3].length) (baseStart_6388594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6388594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6388594 prefixEnd_6388594 := by exact prefixLift 6388594
  have htrace : WordTrace (prefixWord ++ tailWord_6388594) baseStart_6388594 baseEnd_6388594 := by
    simpa [prefixWord, tailWord_6388594, baseEnd_6388594] using wordTrace_append hprefix tailTrace_6388594
  have hstable : (prefixWord ++ tailWord_6388594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6388594).length < 2 ^ (prefixWord ++ tailWord_6388594).sum := by decide
  have hdescent : baseEnd_6388594 < baseStart_6388594 := by decide
  rcases family_descends (prefixWord ++ tailWord_6388594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6388598 : List Nat := [5, 1, 1, 3, 1, 3, 1, 1, 2, 2, 3]
def baseStart_6388598 : Nat := 118140960795 + 6388598 * 2 ^ 59
def prefixEnd_6388598 : Nat := 4983230072969 + 3 ^ 40 * 6388598 * 2
def baseEnd_6388598 : Nat := 3280421482352500814644379

theorem tailTrace_6388598 : CollatzResearch.WordTrace tailWord_6388598 prefixEnd_6388598 3280421482352500814644379 := by
  unfold tailWord_6388598
  simp only [CollatzResearch.WordTrace]
  refine ⟨14563206981825500407358903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 155340874472805337678494965 14563206981825500407358903)
  ·
    refine ⟨21844810472738250611038355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14563206981825500407358903 21844810472738250611038355)
    ·
      refine ⟨32767215709107375916557533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21844810472738250611038355 32767215709107375916557533)
      ·
        refine ⟨12287705890915265968709075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32767215709107375916557533 12287705890915265968709075)
        ·
          refine ⟨18431558836372898953063613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12287705890915265968709075 18431558836372898953063613)
          ·
            refine ⟨6911834563639837107398855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18431558836372898953063613 6911834563639837107398855)
            ·
              refine ⟨10367751845459755661098283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6911834563639837107398855 10367751845459755661098283)
              ·
                refine ⟨15551627768189633491647425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10367751845459755661098283 15551627768189633491647425)
                ·
                  refine ⟨11663720826142225118735569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15551627768189633491647425 11663720826142225118735569)
                  ·
                    refine ⟨8747790619606668839051677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11663720826142225118735569 8747790619606668839051677)
                    ·
                      refine ⟨3280421482352500814644379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8747790619606668839051677 3280421482352500814644379)
                      ·
                        rfl

theorem cell23_6388598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_6388598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6388598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6388598 prefixEnd_6388598 := by exact prefixLift 6388598
  have htrace : WordTrace (prefixWord ++ tailWord_6388598) baseStart_6388598 baseEnd_6388598 := by
    simpa [prefixWord, tailWord_6388598, baseEnd_6388598] using wordTrace_append hprefix tailTrace_6388598
  have hstable : (prefixWord ++ tailWord_6388598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6388598).length < 2 ^ (prefixWord ++ tailWord_6388598).sum := by decide
  have hdescent : baseEnd_6388598 < baseStart_6388598 := by decide
  rcases family_descends (prefixWord ++ tailWord_6388598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6388628 : List Nat := [2, 4, 2, 1, 1, 1, 1, 6, 1, 1, 3]
def baseStart_6388628 : Nat := 118140960795 + 6388628 * 2 ^ 59
def prefixEnd_6388628 : Nat := 4983230072969 + 3 ^ 40 * 6388628 * 2
def baseEnd_6388628 : Nat := 3280436886772135697269241

theorem tailTrace_6388628 : CollatzResearch.WordTrace tailWord_6388628 prefixEnd_6388628 3280436886772135697269241 := by
  unfold tailWord_6388628
  simp only [CollatzResearch.WordTrace]
  refine ⟨116506202949549660820667269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155341603932732881094223025 116506202949549660820667269)
  ·
    refine ⟨21844913053040561403875113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116506202949549660820667269 21844913053040561403875113)
    ·
      refine ⟨16383684789780421052906335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21844913053040561403875113 16383684789780421052906335)
      ·
        refine ⟨24575527184670631579359503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16383684789780421052906335 24575527184670631579359503)
        ·
          refine ⟨36863290777005947369039255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24575527184670631579359503 36863290777005947369039255)
          ·
            refine ⟨55294936165508921053558883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36863290777005947369039255 55294936165508921053558883)
            ·
              refine ⟨82942404248263381580338325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55294936165508921053558883 82942404248263381580338325)
              ·
                refine ⟨3887925199137346011578359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 82942404248263381580338325 3887925199137346011578359)
                ·
                  refine ⟨5831887798706019017367539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3887925199137346011578359 5831887798706019017367539)
                  ·
                    refine ⟨8747831698059028526051309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5831887798706019017367539 8747831698059028526051309)
                    ·
                      refine ⟨3280436886772135697269241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8747831698059028526051309 3280436886772135697269241)
                      ·
                        rfl

theorem cell23_6388628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_6388628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6388628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6388628 prefixEnd_6388628 := by exact prefixLift 6388628
  have htrace : WordTrace (prefixWord ++ tailWord_6388628) baseStart_6388628 baseEnd_6388628 := by
    simpa [prefixWord, tailWord_6388628, baseEnd_6388628] using wordTrace_append hprefix tailTrace_6388628
  have hstable : (prefixWord ++ tailWord_6388628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6388628).length < 2 ^ (prefixWord ++ tailWord_6388628).sum := by decide
  have hdescent : baseEnd_6388628 < baseStart_6388628 := by decide
  rcases family_descends (prefixWord ++ tailWord_6388628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6388744 : List Nat := [2, 1, 3, 2, 1, 3, 1, 1, 2, 4, 3]
def baseStart_6388744 : Nat := 118140960795 + 6388744 * 2 ^ 59
def prefixEnd_6388744 : Nat := 4983230072969 + 3 ^ 40 * 6388744 * 2
def baseEnd_6388744 : Nat := 3280496450528057243418707

theorem tailTrace_6388744 : CollatzResearch.WordTrace tailWord_6388744 prefixEnd_6388744 3280496450528057243418707 := by
  unfold tailWord_6388744
  simp only [CollatzResearch.WordTrace]
  refine ⟨116508318383339536726278643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155344424511119382301704857 116508318383339536726278643)
  ·
    refine ⟨174762477575009305089417965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116508318383339536726278643 174762477575009305089417965)
    ·
      refine ⟨65535929090628489408531737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174762477575009305089417965 65535929090628489408531737)
      ·
        refine ⟨49151946817971367056398803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65535929090628489408531737 49151946817971367056398803)
        ·
          refine ⟨73727920226957050584598205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49151946817971367056398803 73727920226957050584598205)
          ·
            refine ⟨27647970085108893969224327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73727920226957050584598205 27647970085108893969224327)
            ·
              refine ⟨41471955127663340953836491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27647970085108893969224327 41471955127663340953836491)
              ·
                refine ⟨62207932691495011430754737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41471955127663340953836491 62207932691495011430754737)
                ·
                  refine ⟨46655949518621258573066053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62207932691495011430754737 46655949518621258573066053)
                  ·
                    refine ⟨8747990534741485982449885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46655949518621258573066053 8747990534741485982449885)
                    ·
                      refine ⟨3280496450528057243418707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8747990534741485982449885 3280496450528057243418707)
                      ·
                        rfl

theorem cell23_6388744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_6388744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6388744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6388744 prefixEnd_6388744 := by exact prefixLift 6388744
  have htrace : WordTrace (prefixWord ++ tailWord_6388744) baseStart_6388744 baseEnd_6388744 := by
    simpa [prefixWord, tailWord_6388744, baseEnd_6388744] using wordTrace_append hprefix tailTrace_6388744
  have hstable : (prefixWord ++ tailWord_6388744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6388744).length < 2 ^ (prefixWord ++ tailWord_6388744).sum := by decide
  have hdescent : baseEnd_6388744 < baseStart_6388744 := by decide
  rcases family_descends (prefixWord ++ tailWord_6388744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6388794 : List Nat := [3, 1, 1, 1, 3, 1, 2, 4, 2, 5]
def baseStart_6388794 : Nat := 118140960795 + 6388794 * 2 ^ 59
def prefixEnd_6388794 : Nat := 4983230072969 + 3 ^ 40 * 6388794 * 2
def baseEnd_6388794 : Nat := 1093507374853594015931159

theorem tailTrace_6388794 : CollatzResearch.WordTrace tailWord_6388794 prefixEnd_6388794 1093507374853594015931159 := by
  unfold tailWord_6388794
  simp only [CollatzResearch.WordTrace]
  refine ⟨58254615104124482997969359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155345640277665287994584957 58254615104124482997969359)
  ·
    refine ⟨87381922656186724496954039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58254615104124482997969359 87381922656186724496954039)
    ·
      refine ⟨131072883984280086745431059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87381922656186724496954039 131072883984280086745431059)
      ·
        refine ⟨196609325976420130118146589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131072883984280086745431059 196609325976420130118146589)
        ·
          refine ⟨73728497241157548794304971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196609325976420130118146589 73728497241157548794304971)
          ·
            refine ⟨110592745861736323191457457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73728497241157548794304971 110592745861736323191457457)
            ·
              refine ⟨82944559396302242393593093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110592745861736323191457457 82944559396302242393593093)
              ·
                refine ⟨15552104886806670448798705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82944559396302242393593093 15552104886806670448798705)
                ·
                  refine ⟨11664078665105002836599029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15552104886806670448798705 11664078665105002836599029)
                  ·
                    refine ⟨1093507374853594015931159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11664078665105002836599029 1093507374853594015931159)
                    ·
                      rfl

theorem cell23_6388794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4, 2, 5].length) (baseStart_6388794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6388794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6388794 prefixEnd_6388794 := by exact prefixLift 6388794
  have htrace : WordTrace (prefixWord ++ tailWord_6388794) baseStart_6388794 baseEnd_6388794 := by
    simpa [prefixWord, tailWord_6388794, baseEnd_6388794] using wordTrace_append hprefix tailTrace_6388794
  have hstable : (prefixWord ++ tailWord_6388794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6388794).length < 2 ^ (prefixWord ++ tailWord_6388794).sum := by decide
  have hdescent : baseEnd_6388794 < baseStart_6388794 := by decide
  rcases family_descends (prefixWord ++ tailWord_6388794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6388798 : List Nat := [4, 2, 1, 3, 1, 1, 2, 4, 5]
def baseStart_6388798 : Nat := 118140960795 + 6388798 * 2 ^ 59
def prefixEnd_6388798 : Nat := 4983230072969 + 3 ^ 40 * 6388798 * 2
def baseEnd_6388798 : Nat := 364502686498155559127051

theorem tailTrace_6388798 : CollatzResearch.WordTrace tailWord_6388798 prefixEnd_6388798 364502686498155559127051 := by
  unfold tailWord_6388798
  simp only [CollatzResearch.WordTrace]
  refine ⟨29127325788560430084377881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155345737538988960450015365 29127325788560430084377881)
  ·
    refine ⟨21845494341420322563283411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29127325788560430084377881 21845494341420322563283411)
    ·
      refine ⟨32768241512130483844925117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21845494341420322563283411 32768241512130483844925117)
      ·
        refine ⟨12288090567048931441846919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32768241512130483844925117 12288090567048931441846919)
        ·
          refine ⟨18432135850573397162770379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12288090567048931441846919 18432135850573397162770379)
          ·
            refine ⟨27648203775860095744155569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18432135850573397162770379 27648203775860095744155569)
            ·
              refine ⟨20736152831895071808116677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27648203775860095744155569 20736152831895071808116677)
              ·
                refine ⟨3888028655980325964021877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20736152831895071808116677 3888028655980325964021877)
                ·
                  refine ⟨364502686498155559127051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3888028655980325964021877 364502686498155559127051)
                  ·
                    rfl

theorem cell23_6388798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 4, 5].length) (baseStart_6388798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6388798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6388798 prefixEnd_6388798 := by exact prefixLift 6388798
  have htrace : WordTrace (prefixWord ++ tailWord_6388798) baseStart_6388798 baseEnd_6388798 := by
    simpa [prefixWord, tailWord_6388798, baseEnd_6388798] using wordTrace_append hprefix tailTrace_6388798
  have hstable : (prefixWord ++ tailWord_6388798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6388798).length < 2 ^ (prefixWord ++ tailWord_6388798).sum := by decide
  have hdescent : baseEnd_6388798 < baseStart_6388798 := by decide
  rcases family_descends (prefixWord ++ tailWord_6388798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6388814 : List Nat := [4, 1, 1, 1, 1, 3, 1, 1, 3, 3, 4]
def baseStart_6388814 : Nat := 118140960795 + 6388814 * 2 ^ 59
def prefixEnd_6388814 : Nat := 4983230072969 + 3 ^ 40 * 6388814 * 2
def baseEnd_6388814 : Nat := 3280532394173871969543385

theorem tailTrace_6388814 : CollatzResearch.WordTrace tailWord_6388814 prefixEnd_6388814 3280532394173871969543385 := by
  unfold tailWord_6388814
  simp only [CollatzResearch.WordTrace]
  refine ⟨29127398734553184425950687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155346126584283650271736997 29127398734553184425950687)
  ·
    refine ⟨43691098101829776638926031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29127398734553184425950687 43691098101829776638926031)
    ·
      refine ⟨65536647152744664958389047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43691098101829776638926031 65536647152744664958389047)
      ·
        refine ⟨98304970729116997437583571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65536647152744664958389047 98304970729116997437583571)
        ·
          refine ⟨147457456093675496156375357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98304970729116997437583571 147457456093675496156375357)
          ·
            refine ⟨55296546035128311058640759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147457456093675496156375357 55296546035128311058640759)
            ·
              refine ⟨82944819052692466587961139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55296546035128311058640759 82944819052692466587961139)
              ·
                refine ⟨124417228579038699881941709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82944819052692466587961139 124417228579038699881941709)
                ·
                  refine ⟨46656460717139512455728141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 124417228579038699881941709 46656460717139512455728141)
                  ·
                    refine ⟨17496172768927317170898053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46656460717139512455728141 17496172768927317170898053)
                    ·
                      refine ⟨3280532394173871969543385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17496172768927317170898053 3280532394173871969543385)
                      ·
                        rfl

theorem cell23_6388814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_6388814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6388814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6388814 prefixEnd_6388814 := by exact prefixLift 6388814
  have htrace : WordTrace (prefixWord ++ tailWord_6388814) baseStart_6388814 baseEnd_6388814 := by
    simpa [prefixWord, tailWord_6388814, baseEnd_6388814] using wordTrace_append hprefix tailTrace_6388814
  have hstable : (prefixWord ++ tailWord_6388814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6388814).length < 2 ^ (prefixWord ++ tailWord_6388814).sum := by decide
  have hdescent : baseEnd_6388814 < baseStart_6388814 := by decide
  rcases family_descends (prefixWord ++ tailWord_6388814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6388909 : List Nat := [1, 5, 2, 1, 3, 2, 2, 2, 1, 4]
def baseStart_6388909 : Nat := 118140960795 + 6388909 * 2 ^ 59
def prefixEnd_6388909 : Nat := 4983230072969 + 3 ^ 40 * 6388909 * 2
def baseEnd_6388909 : Nat := 1093527058278683032618483

theorem tailTrace_6388909 : CollatzResearch.WordTrace tailWord_6388909 prefixEnd_6388909 1093527058278683032618483 := by
  unfold tailWord_6388909
  simp only [CollatzResearch.WordTrace]
  refine ⟨233022654811081306632313781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155348436540720871088209187 233022654811081306632313781)
  ·
    refine ⟨21845873888538872496779417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 233022654811081306632313781 21845873888538872496779417)
    ·
      refine ⟨16384405416404154372584563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21845873888538872496779417 16384405416404154372584563)
      ·
        refine ⟨24576608124606231558876845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16384405416404154372584563 24576608124606231558876845)
        ·
          refine ⟨9216228046727336834578817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24576608124606231558876845 9216228046727336834578817)
          ·
            refine ⟨6912171035045502625934113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9216228046727336834578817 6912171035045502625934113)
            ·
              refine ⟨5184128276284126969450585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6912171035045502625934113 5184128276284126969450585)
              ·
                refine ⟨3888096207213095227087939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5184128276284126969450585 3888096207213095227087939)
                ·
                  refine ⟨5832144310819642840631909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3888096207213095227087939 5832144310819642840631909)
                  ·
                    refine ⟨1093527058278683032618483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5832144310819642840631909 1093527058278683032618483)
                    ·
                      rfl

theorem cell23_6388909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_6388909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6388909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6388909 prefixEnd_6388909 := by exact prefixLift 6388909
  have htrace : WordTrace (prefixWord ++ tailWord_6388909) baseStart_6388909 baseEnd_6388909 := by
    simpa [prefixWord, tailWord_6388909, baseEnd_6388909] using wordTrace_append hprefix tailTrace_6388909
  have hstable : (prefixWord ++ tailWord_6388909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6388909).length < 2 ^ (prefixWord ++ tailWord_6388909).sum := by decide
  have hdescent : baseEnd_6388909 < baseStart_6388909 := by decide
  rcases family_descends (prefixWord ++ tailWord_6388909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6388921 : List Nat := [1, 2, 1, 4, 1, 3, 1, 2, 3, 1, 4]
def baseStart_6388921 : Nat := 118140960795 + 6388921 * 2 ^ 59
def prefixEnd_6388921 : Nat := 4983230072969 + 3 ^ 40 * 6388921 * 2
def baseEnd_6388921 : Nat := 3280587336603903050905393

theorem tailTrace_6388921 : CollatzResearch.WordTrace tailWord_6388921 prefixEnd_6388921 3280587336603903050905393 := by
  unfold tailWord_6388921
  simp only [CollatzResearch.WordTrace]
  refine ⟨233023092487037832681750617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155348728324691888454500411 233023092487037832681750617)
  ·
    refine ⟨174767319365278374511312963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233023092487037832681750617 174767319365278374511312963)
    ·
      refine ⟨262150979047917561766969445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174767319365278374511312963 262150979047917561766969445)
      ·
        refine ⟨49153308571484542831306771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 262150979047917561766969445 49153308571484542831306771)
        ·
          refine ⟨73729962857226814246960157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49153308571484542831306771 73729962857226814246960157)
          ·
            refine ⟨27648736071460055342610059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73729962857226814246960157 27648736071460055342610059)
            ·
              refine ⟨41473104107190083013915089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27648736071460055342610059 41473104107190083013915089)
              ·
                refine ⟨31104828080392562260436317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41473104107190083013915089 31104828080392562260436317)
                ·
                  refine ⟨11664310530147210847663619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31104828080392562260436317 11664310530147210847663619)
                  ·
                    refine ⟨17496465795220816271495429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11664310530147210847663619 17496465795220816271495429)
                    ·
                      refine ⟨3280587336603903050905393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17496465795220816271495429 3280587336603903050905393)
                      ·
                        rfl

theorem cell23_6388921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_6388921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6388921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6388921 prefixEnd_6388921 := by exact prefixLift 6388921
  have htrace : WordTrace (prefixWord ++ tailWord_6388921) baseStart_6388921 baseEnd_6388921 := by
    simpa [prefixWord, tailWord_6388921, baseEnd_6388921] using wordTrace_append hprefix tailTrace_6388921
  have hstable : (prefixWord ++ tailWord_6388921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6388921).length < 2 ^ (prefixWord ++ tailWord_6388921).sum := by decide
  have hdescent : baseEnd_6388921 < baseStart_6388921 := by decide
  rcases family_descends (prefixWord ++ tailWord_6388921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6388942 : List Nat := [4, 1, 1, 1, 5, 2, 1, 1, 2, 3, 2]
def baseStart_6388942 : Nat := 118140960795 + 6388942 * 2 ^ 59
def prefixEnd_6388942 : Nat := 4983230072969 + 3 ^ 40 * 6388942 * 2
def baseEnd_6388942 : Nat := 3280598119697647468742797

theorem tailTrace_6388942 : CollatzResearch.WordTrace tailWord_6388942 prefixEnd_6388942 3280598119697647468742797 := by
  unfold tailWord_6388942
  simp only [CollatzResearch.WordTrace]
  refine ⟨29127982302495219158533135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155349238946641168845510053 29127982302495219158533135)
  ·
    refine ⟨43691973453742828737799703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29127982302495219158533135 43691973453742828737799703)
    ·
      refine ⟨65537960180614243106699555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43691973453742828737799703 65537960180614243106699555)
      ·
        refine ⟨98306940270921364660049333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65537960180614243106699555 98306940270921364660049333)
        ·
          refine ⟨9216275650398877936879625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 98306940270921364660049333 9216275650398877936879625)
          ·
            refine ⟨6912206737799158452659719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9216275650398877936879625 6912206737799158452659719)
            ·
              refine ⟨10368310106698737678989579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6912206737799158452659719 10368310106698737678989579)
              ·
                refine ⟨15552465160048106518484369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10368310106698737678989579 15552465160048106518484369)
                ·
                  refine ⟨11664348870036079888863277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15552465160048106518484369 11664348870036079888863277)
                  ·
                    refine ⟨4374130826263529958323729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11664348870036079888863277 4374130826263529958323729)
                    ·
                      refine ⟨3280598119697647468742797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4374130826263529958323729 3280598119697647468742797)
                      ·
                        rfl

theorem cell23_6388942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 1, 2, 3, 2].length) (baseStart_6388942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6388942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6388942 prefixEnd_6388942 := by exact prefixLift 6388942
  have htrace : WordTrace (prefixWord ++ tailWord_6388942) baseStart_6388942 baseEnd_6388942 := by
    simpa [prefixWord, tailWord_6388942, baseEnd_6388942] using wordTrace_append hprefix tailTrace_6388942
  have hstable : (prefixWord ++ tailWord_6388942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6388942).length < 2 ^ (prefixWord ++ tailWord_6388942).sum := by decide
  have hdescent : baseEnd_6388942 < baseStart_6388942 := by decide
  rcases family_descends (prefixWord ++ tailWord_6388942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6388951 : List Nat := [1, 1, 3, 2, 1, 2, 4, 2, 1, 2, 4]
def baseStart_6388951 : Nat := 118140960795 + 6388951 * 2 ^ 59
def prefixEnd_6388951 : Nat := 4983230072969 + 3 ^ 40 * 6388951 * 2
def baseEnd_6388951 : Nat := 3280602741023537933530255

theorem tailTrace_6388951 : CollatzResearch.WordTrace tailWord_6388951 prefixEnd_6388951 3280602741023537933530255 := by
  unfold tailWord_6388951
  simp only [CollatzResearch.WordTrace]
  refine ⟨233024186676929147805342707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155349457784619431870228471 233024186676929147805342707)
  ·
    refine ⟨349536280015393721708014061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233024186676929147805342707 349536280015393721708014061)
    ·
      refine ⟨131076105005772645640505273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 349536280015393721708014061 131076105005772645640505273)
      ·
        refine ⟨98307078754329484230378955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131076105005772645640505273 98307078754329484230378955)
        ·
          refine ⟨147460618131494226345568433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98307078754329484230378955 147460618131494226345568433)
          ·
            refine ⟨110595463598620669759176325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147460618131494226345568433 110595463598620669759176325)
            ·
              refine ⟨20736649424741375579845561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110595463598620669759176325 20736649424741375579845561)
              ·
                refine ⟨15552487068556031684884171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20736649424741375579845561 15552487068556031684884171)
                ·
                  refine ⟨23328730602834047527326257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15552487068556031684884171 23328730602834047527326257)
                  ·
                    refine ⟨17496547952125535645494693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23328730602834047527326257 17496547952125535645494693)
                    ·
                      refine ⟨3280602741023537933530255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17496547952125535645494693 3280602741023537933530255)
                      ·
                        rfl

theorem cell23_6388951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 2, 1, 2, 4].length) (baseStart_6388951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6388951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6388951 prefixEnd_6388951 := by exact prefixLift 6388951
  have htrace : WordTrace (prefixWord ++ tailWord_6388951) baseStart_6388951 baseEnd_6388951 := by
    simpa [prefixWord, tailWord_6388951, baseEnd_6388951] using wordTrace_append hprefix tailTrace_6388951
  have hstable : (prefixWord ++ tailWord_6388951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6388951).length < 2 ^ (prefixWord ++ tailWord_6388951).sum := by decide
  have hdescent : baseEnd_6388951 < baseStart_6388951 := by decide
  rcases family_descends (prefixWord ++ tailWord_6388951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6388952 : List Nat := [2, 1, 2, 2, 6, 1, 2, 1, 1, 5]
def baseStart_6388952 : Nat := 118140960795 + 6388952 * 2 ^ 59
def prefixEnd_6388952 : Nat := 4983230072969 + 3 ^ 40 * 6388952 * 2
def baseEnd_6388952 : Nat := 1093534418168064143205917

theorem tailTrace_6388952 : CollatzResearch.WordTrace tailWord_6388952 prefixEnd_6388952 1093534418168064143205917 := by
  unfold tailWord_6388952
  simp only [CollatzResearch.WordTrace]
  refine ⟨116512111574962762488064555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155349482099950349984086073 116512111574962762488064555)
  ·
    refine ⟨174768167362444143732096833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116512111574962762488064555 174768167362444143732096833)
    ·
      refine ⟨131076125521833107799072625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174768167362444143732096833 131076125521833107799072625)
      ·
        refine ⟨98307094141374830849304469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131076125521833107799072625 98307094141374830849304469)
        ·
          refine ⟨4608145037876945196061147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 98307094141374830849304469 4608145037876945196061147)
          ·
            refine ⟨6912217556815417794091721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4608145037876945196061147 6912217556815417794091721)
            ·
              refine ⟨5184163167611563345568791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6912217556815417794091721 5184163167611563345568791)
              ·
                refine ⟨7776244751417345018353187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5184163167611563345568791 7776244751417345018353187)
                ·
                  refine ⟨11664367127126017527529781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7776244751417345018353187 11664367127126017527529781)
                  ·
                    refine ⟨1093534418168064143205917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11664367127126017527529781 1093534418168064143205917)
                    ·
                      rfl

theorem cell23_6388952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 2, 1, 1, 5].length) (baseStart_6388952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6388952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6388952 prefixEnd_6388952 := by exact prefixLift 6388952
  have htrace : WordTrace (prefixWord ++ tailWord_6388952) baseStart_6388952 baseEnd_6388952 := by
    simpa [prefixWord, tailWord_6388952, baseEnd_6388952] using wordTrace_append hprefix tailTrace_6388952
  have hstable : (prefixWord ++ tailWord_6388952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6388952).length < 2 ^ (prefixWord ++ tailWord_6388952).sum := by decide
  have hdescent : baseEnd_6388952 < baseStart_6388952 := by decide
  rcases family_descends (prefixWord ++ tailWord_6388952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6388972 : List Nat := [2, 2, 1, 1, 2, 4, 2, 4, 1, 2, 2]
def baseStart_6388972 : Nat := 118140960795 + 6388972 * 2 ^ 59
def prefixEnd_6388972 : Nat := 4983230072969 + 3 ^ 40 * 6388972 * 2
def baseEnd_6388972 : Nat := 3280613524117282351367659

theorem tailTrace_6388972 : CollatzResearch.WordTrace tailWord_6388972 prefixEnd_6388972 3280613524117282351367659 := by
  unfold tailWord_6388972
  simp only [CollatzResearch.WordTrace]
  refine ⟨116512476304926534195928585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155349968406568712261238113 116512476304926534195928585)
  ·
    refine ⟨87384357228694900646946439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116512476304926534195928585 87384357228694900646946439)
    ·
      refine ⟨131076535843042350970419659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87384357228694900646946439 131076535843042350970419659)
      ·
        refine ⟨196614803764563526455629489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131076535843042350970419659 196614803764563526455629489)
        ·
          refine ⟨147461102823422644841722117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196614803764563526455629489 147461102823422644841722117)
          ·
            refine ⟨27648956779391745907822897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 147461102823422644841722117 27648956779391745907822897)
            ·
              refine ⟨20736717584543809430867173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27648956779391745907822897 20736717584543809430867173)
              ·
                refine ⟨3888134547101964268287595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20736717584543809430867173 3888134547101964268287595)
                ·
                  refine ⟨5832201820652946402431393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3888134547101964268287595 5832201820652946402431393)
                  ·
                    refine ⟨4374151365489709801823545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5832201820652946402431393 4374151365489709801823545)
                    ·
                      refine ⟨3280613524117282351367659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4374151365489709801823545 3280613524117282351367659)
                      ·
                        rfl

theorem cell23_6388972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 4, 1, 2, 2].length) (baseStart_6388972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6388972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6388972 prefixEnd_6388972 := by exact prefixLift 6388972
  have htrace : WordTrace (prefixWord ++ tailWord_6388972) baseStart_6388972 baseEnd_6388972 := by
    simpa [prefixWord, tailWord_6388972, baseEnd_6388972] using wordTrace_append hprefix tailTrace_6388972
  have hstable : (prefixWord ++ tailWord_6388972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6388972).length < 2 ^ (prefixWord ++ tailWord_6388972).sum := by decide
  have hdescent : baseEnd_6388972 < baseStart_6388972 := by decide
  rcases family_descends (prefixWord ++ tailWord_6388972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6389015 : List Nat := [1, 1, 3, 4, 1, 1, 1, 5, 1, 3, 2]
def baseStart_6389015 : Nat := 118140960795 + 6389015 * 2 ^ 59
def prefixEnd_6389015 : Nat := 4983230072969 + 3 ^ 40 * 6389015 * 2
def baseEnd_6389015 : Nat := 3280635603785425683129961

theorem tailTrace_6389015 : CollatzResearch.WordTrace tailWord_6389015 prefixEnd_6389015 3280635603785425683129961 := by
  unfold tailWord_6389015
  simp only [CollatzResearch.WordTrace]
  refine ⟨233026520948697286735672499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155351013965798191157114999 233026520948697286735672499)
  ·
    refine ⟨349539781423045930103508749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233026520948697286735672499 349539781423045930103508749)
    ·
      refine ⟨131077418033642223788815781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 349539781423045930103508749 131077418033642223788815781)
      ·
        refine ⟨24577015881307916960402959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131077418033642223788815781 24577015881307916960402959)
        ·
          refine ⟨36865523821961875440604439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24577015881307916960402959 36865523821961875440604439)
          ·
            refine ⟨55298285732942813160906659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36865523821961875440604439 55298285732942813160906659)
            ·
              refine ⟨82947428599414219741359989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55298285732942813160906659 82947428599414219741359989)
              ·
                refine ⟨7776321431195083100752499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82947428599414219741359989 7776321431195083100752499)
                ·
                  refine ⟨11664482146792624651128749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7776321431195083100752499 11664482146792624651128749)
                  ·
                    refine ⟨4374180805047234244173281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11664482146792624651128749 4374180805047234244173281)
                    ·
                      refine ⟨3280635603785425683129961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4374180805047234244173281 3280635603785425683129961)
                      ·
                        rfl

theorem cell23_6389015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_6389015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6389015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6389015 prefixEnd_6389015 := by exact prefixLift 6389015
  have htrace : WordTrace (prefixWord ++ tailWord_6389015) baseStart_6389015 baseEnd_6389015 := by
    simpa [prefixWord, tailWord_6389015, baseEnd_6389015] using wordTrace_append hprefix tailTrace_6389015
  have hstable : (prefixWord ++ tailWord_6389015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6389015).length < 2 ^ (prefixWord ++ tailWord_6389015).sum := by decide
  have hdescent : baseEnd_6389015 < baseStart_6389015 := by decide
  rcases family_descends (prefixWord ++ tailWord_6389015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6389049 : List Nat := [1, 2, 1, 6, 2, 2, 1, 2, 1, 3, 2]
def baseStart_6389049 : Nat := 118140960795 + 6389049 * 2 ^ 59
def prefixEnd_6389049 : Nat := 4983230072969 + 3 ^ 40 * 6389049 * 2
def baseEnd_6389049 : Nat := 3280653062127678550104805

theorem tailTrace_6389049 : CollatzResearch.WordTrace tailWord_6389049 prefixEnd_6389049 3280653062127678550104805 := by
  unfold tailWord_6389049
  simp only [CollatzResearch.WordTrace]
  refine ⟨233027761030574110542410201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155351840687049407028273467 233027761030574110542410201)
  ·
    refine ⟨174770820772930582906807651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233027761030574110542410201 174770820772930582906807651)
    ·
      refine ⟨262156231159395874360211477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174770820772930582906807651 262156231159395874360211477)
      ·
        refine ⟨12288573335596681610634913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 262156231159395874360211477 12288573335596681610634913)
        ·
          refine ⟨9216430001697511207976185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12288573335596681610634913 9216430001697511207976185)
          ·
            refine ⟨6912322501273133405982139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9216430001697511207976185 6912322501273133405982139)
            ·
              refine ⟨10368483751909700108973209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6912322501273133405982139 10368483751909700108973209)
              ·
                refine ⟨7776362813932275081729907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10368483751909700108973209 7776362813932275081729907)
                ·
                  refine ⟨11664544220898412622594861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7776362813932275081729907 11664544220898412622594861)
                  ·
                    refine ⟨4374204082836904733473073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11664544220898412622594861 4374204082836904733473073)
                    ·
                      refine ⟨3280653062127678550104805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4374204082836904733473073 3280653062127678550104805)
                      ·
                        rfl

theorem cell23_6389049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_6389049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6389049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6389049 prefixEnd_6389049 := by exact prefixLift 6389049
  have htrace : WordTrace (prefixWord ++ tailWord_6389049) baseStart_6389049 baseEnd_6389049 := by
    simpa [prefixWord, tailWord_6389049, baseEnd_6389049] using wordTrace_append hprefix tailTrace_6389049
  have hstable : (prefixWord ++ tailWord_6389049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6389049).length < 2 ^ (prefixWord ++ tailWord_6389049).sum := by decide
  have hdescent : baseEnd_6389049 < baseStart_6389049 := by decide
  rcases family_descends (prefixWord ++ tailWord_6389049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6389095 : List Nat := [1, 1, 5, 1, 4, 1, 1, 1, 2, 3, 3]
def baseStart_6389095 : Nat := 118140960795 + 6389095 * 2 ^ 59
def prefixEnd_6389095 : Nat := 4983230072969 + 3 ^ 40 * 6389095 * 2
def baseEnd_6389095 : Nat := 3280676682237785370129593

theorem tailTrace_6389095 : CollatzResearch.WordTrace tailWord_6389095 prefixEnd_6389095 3280676682237785370129593 := by
  unfold tailWord_6389095
  simp only [CollatzResearch.WordTrace]
  refine ⟨233029438788407460398584739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155352959192271640265723159 233029438788407460398584739)
  ·
    refine ⟨349544158182611190597877109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233029438788407460398584739 349544158182611190597877109)
    ·
      refine ⟨32769764829619799118550979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 349544158182611190597877109 32769764829619799118550979)
      ·
        refine ⟨49154647244429698677826469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32769764829619799118550979 49154647244429698677826469)
        ·
          refine ⟨9216496358330568502092463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49154647244429698677826469 9216496358330568502092463)
          ·
            refine ⟨13824744537495852753138695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9216496358330568502092463 13824744537495852753138695)
            ·
              refine ⟨20737116806243779129708043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13824744537495852753138695 20737116806243779129708043)
              ·
                refine ⟨31105675209365668694562065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20737116806243779129708043 31105675209365668694562065)
                ·
                  refine ⟨23329256407024251520921549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31105675209365668694562065 23329256407024251520921549)
                  ·
                    refine ⟨8748471152634094320345581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23329256407024251520921549 8748471152634094320345581)
                    ·
                      refine ⟨3280676682237785370129593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8748471152634094320345581 3280676682237785370129593)
                      ·
                        rfl

theorem cell23_6389095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_6389095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6389095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6389095 prefixEnd_6389095 := by exact prefixLift 6389095
  have htrace : WordTrace (prefixWord ++ tailWord_6389095) baseStart_6389095 baseEnd_6389095 := by
    simpa [prefixWord, tailWord_6389095, baseEnd_6389095] using wordTrace_append hprefix tailTrace_6389095
  have hstable : (prefixWord ++ tailWord_6389095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6389095).length < 2 ^ (prefixWord ++ tailWord_6389095).sum := by decide
  have hdescent : baseEnd_6389095 < baseStart_6389095 := by decide
  rcases family_descends (prefixWord ++ tailWord_6389095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6389131 : List Nat := [1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 6]
def baseStart_6389131 : Nat := 118140960795 + 6389131 * 2 ^ 59
def prefixEnd_6389131 : Nat := 4983230072969 + 3 ^ 40 * 6389131 * 2
def baseEnd_6389131 : Nat := 3280695167541347229279427

theorem tailTrace_6389131 : CollatzResearch.WordTrace tailWord_6389131 prefixEnd_6389131 3280695167541347229279427 := by
  unfold tailWord_6389131
  simp only [CollatzResearch.WordTrace]
  refine ⟨233030751816277038546895247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155353834544184692364596831 233030751816277038546895247)
  ·
    refine ⟨349546127724415557820342871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233030751816277038546895247 349546127724415557820342871)
    ·
      refine ⟨524319191586623336730514307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349546127724415557820342871 524319191586623336730514307)
      ·
        refine ⟨786478787379935005095771461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 524319191586623336730514307 786478787379935005095771461)
        ·
          refine ⟨147464772633737813455457149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 786478787379935005095771461 147464772633737813455457149)
          ·
            refine ⟨55299289737651680045796431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147464772633737813455457149 55299289737651680045796431)
            ·
              refine ⟨82948934606477520068694647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55299289737651680045796431 82948934606477520068694647)
              ·
                refine ⟨124423401909716280103041971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82948934606477520068694647 124423401909716280103041971)
                ·
                  refine ⟨186635102864574420154562957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124423401909716280103041971 186635102864574420154562957)
                  ·
                    refine ⟨69988163574215407557961109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 186635102864574420154562957 69988163574215407557961109)
                    ·
                      refine ⟨3280695167541347229279427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69988163574215407557961109 3280695167541347229279427)
                      ·
                        rfl

theorem cell23_6389131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 6].length) (baseStart_6389131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6389131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6389131 prefixEnd_6389131 := by exact prefixLift 6389131
  have htrace : WordTrace (prefixWord ++ tailWord_6389131) baseStart_6389131 baseEnd_6389131 := by
    simpa [prefixWord, tailWord_6389131, baseEnd_6389131] using wordTrace_append hprefix tailTrace_6389131
  have hstable : (prefixWord ++ tailWord_6389131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6389131).length < 2 ^ (prefixWord ++ tailWord_6389131).sum := by decide
  have hdescent : baseEnd_6389131 < baseStart_6389131 := by decide
  rcases family_descends (prefixWord ++ tailWord_6389131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6389145 : List Nat := [1, 2, 1, 2, 1, 6, 2, 1, 3, 4]
def baseStart_6389145 : Nat := 118140960795 + 6389145 * 2 ^ 59
def prefixEnd_6389145 : Nat := 4983230072969 + 3 ^ 40 * 6389145 * 2
def baseEnd_6389145 : Nat := 1093567452090170058168121

theorem tailTrace_6389145 : CollatzResearch.WordTrace tailWord_6389145 prefixEnd_6389145 1093567452090170058168121 := by
  unfold tailWord_6389145
  simp only [CollatzResearch.WordTrace]
  refine ⟨233031262438226318937904889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155354174958817545958603259 233031262438226318937904889)
  ·
    refine ⟨174773446828669739203428667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233031262438226318937904889 174773446828669739203428667)
    ·
      refine ⟨262160170243004608805143001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174773446828669739203428667 262160170243004608805143001)
      ·
        refine ⟨196620127682253456603857251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262160170243004608805143001 196620127682253456603857251)
        ·
          refine ⟨294930191523380184905785877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196620127682253456603857251 294930191523380184905785877)
          ·
            refine ⟨13824852727658446167458713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 294930191523380184905785877 13824852727658446167458713)
            ·
              refine ⟨10368639545743834625594035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13824852727658446167458713 10368639545743834625594035)
              ·
                refine ⟨15552959318615751938391053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10368639545743834625594035 15552959318615751938391053)
                ·
                  refine ⟨5832359744480906976896645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15552959318615751938391053 5832359744480906976896645)
                  ·
                    refine ⟨1093567452090170058168121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5832359744480906976896645 1093567452090170058168121)
                    ·
                      rfl

theorem cell23_6389145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 1, 3, 4].length) (baseStart_6389145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6389145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6389145 prefixEnd_6389145 := by exact prefixLift 6389145
  have htrace : WordTrace (prefixWord ++ tailWord_6389145) baseStart_6389145 baseEnd_6389145 := by
    simpa [prefixWord, tailWord_6389145, baseEnd_6389145] using wordTrace_append hprefix tailTrace_6389145
  have hstable : (prefixWord ++ tailWord_6389145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6389145).length < 2 ^ (prefixWord ++ tailWord_6389145).sum := by decide
  have hdescent : baseEnd_6389145 < baseStart_6389145 := by decide
  rcases family_descends (prefixWord ++ tailWord_6389145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6389171 : List Nat := [1, 1, 1, 2, 3, 1, 1, 2, 2, 9]
def baseStart_6389171 : Nat := 118140960795 + 6389171 * 2 ^ 59
def prefixEnd_6389171 : Nat := 4983230072969 + 3 ^ 40 * 6389171 * 2
def baseEnd_6389171 : Nat := 1093571902255842357593081

theorem tailTrace_6389171 : CollatzResearch.WordTrace tailWord_6389171 prefixEnd_6389171 1093571902255842357593081 := by
  unfold tailWord_6389171
  simp only [CollatzResearch.WordTrace]
  refine ⟨233032210736132125378351367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155354807157421416918900911 233032210736132125378351367)
  ·
    refine ⟨349548316104198188067527051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233032210736132125378351367 349548316104198188067527051)
    ·
      refine ⟨524322474156297282101290577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349548316104198188067527051 524322474156297282101290577)
      ·
        refine ⟨393241855617222961575967933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 524322474156297282101290577 393241855617222961575967933)
        ·
          refine ⟨147465695856458610590987975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 393241855617222961575967933 147465695856458610590987975)
          ·
            refine ⟨221198543784687915886481963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147465695856458610590987975 221198543784687915886481963)
            ·
              refine ⟨331797815677031873829722945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221198543784687915886481963 331797815677031873829722945)
              ·
                refine ⟨248848361757773905372292209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 331797815677031873829722945 248848361757773905372292209)
                ·
                  refine ⟨186636271318330429029219157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 248848361757773905372292209 186636271318330429029219157)
                  ·
                    refine ⟨1093571902255842357593081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 186636271318330429029219157 1093571902255842357593081)
                    ·
                      rfl

theorem cell23_6389171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 9].length) (baseStart_6389171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6389171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6389171 prefixEnd_6389171 := by exact prefixLift 6389171
  have htrace : WordTrace (prefixWord ++ tailWord_6389171) baseStart_6389171 baseEnd_6389171 := by
    simpa [prefixWord, tailWord_6389171, baseEnd_6389171] using wordTrace_append hprefix tailTrace_6389171
  have hstable : (prefixWord ++ tailWord_6389171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6389171).length < 2 ^ (prefixWord ++ tailWord_6389171).sum := by decide
  have hdescent : baseEnd_6389171 < baseStart_6389171 := by decide
  rcases family_descends (prefixWord ++ tailWord_6389171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6389195 : List Nat := [1, 1, 1, 1, 3, 3, 3, 1, 4, 3, 2]
def baseStart_6389195 : Nat := 118140960795 + 6389195 * 2 ^ 59
def prefixEnd_6389195 : Nat := 4983230072969 + 3 ^ 40 * 6389195 * 2
def baseEnd_6389195 : Nat := 3280728030303234978879133

theorem tailTrace_6389195 : CollatzResearch.WordTrace tailWord_6389195 prefixEnd_6389195 3280728030303234978879133 := by
  unfold tailWord_6389195
  simp only [CollatzResearch.WordTrace]
  refine ⟨233033086088045177477225039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155355390725363451651483359 233033086088045177477225039)
  ·
    refine ⟨349549629132067766215837559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233033086088045177477225039 349549629132067766215837559)
    ·
      refine ⟨524324443698101649323756339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349549629132067766215837559 524324443698101649323756339)
      ·
        refine ⟨786486665547152473985634509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 524324443698101649323756339 786486665547152473985634509)
        ·
          refine ⟨294932499580182177744612941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 786486665547152473985634509 294932499580182177744612941)
          ·
            refine ⟨110599687342568316654229853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 294932499580182177744612941 110599687342568316654229853)
            ·
              refine ⟨41474882753463118745336195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110599687342568316654229853 41474882753463118745336195)
              ·
                refine ⟨62212324130194678118004293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41474882753463118745336195 62212324130194678118004293)
                ·
                  refine ⟨11664810774411502147125805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62212324130194678118004293 11664810774411502147125805)
                  ·
                    refine ⟨4374304040404313305172177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11664810774411502147125805 4374304040404313305172177)
                    ·
                      refine ⟨3280728030303234978879133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4374304040404313305172177 3280728030303234978879133)
                      ·
                        rfl

theorem cell23_6389195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 4, 3, 2].length) (baseStart_6389195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6389195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6389195 prefixEnd_6389195 := by exact prefixLift 6389195
  have htrace : WordTrace (prefixWord ++ tailWord_6389195) baseStart_6389195 baseEnd_6389195 := by
    simpa [prefixWord, tailWord_6389195, baseEnd_6389195] using wordTrace_append hprefix tailTrace_6389195
  have hstable : (prefixWord ++ tailWord_6389195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6389195).length < 2 ^ (prefixWord ++ tailWord_6389195).sum := by decide
  have hdescent : baseEnd_6389195 < baseStart_6389195 := by decide
  rcases family_descends (prefixWord ++ tailWord_6389195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6389242 : List Nat := [3, 1, 1, 1, 1, 2, 7, 1, 1, 1, 4]
def baseStart_6389242 : Nat := 118140960795 + 6389242 * 2 ^ 59
def prefixEnd_6389242 : Nat := 4983230072969 + 3 ^ 40 * 6389242 * 2
def baseEnd_6389242 : Nat := 3280752163893996294991417

theorem tailTrace_6389242 : CollatzResearch.WordTrace tailWord_6389242 prefixEnd_6389242 3280752163893996294991417 := by
  unfold tailWord_6389242
  simp only [CollatzResearch.WordTrace]
  refine ⟨58258700079718726126046495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155356533545916603002790653 58258700079718726126046495)
  ·
    refine ⟨87388050119578089189069743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58258700079718726126046495 87388050119578089189069743)
    ·
      refine ⟨131082075179367133783604615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87388050119578089189069743 131082075179367133783604615)
      ·
        refine ⟨196623112769050700675406923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131082075179367133783604615 196623112769050700675406923)
        ·
          refine ⟨294934669153576051013110385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196623112769050700675406923 294934669153576051013110385)
          ·
            refine ⟨221201001865182038259832789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 294934669153576051013110385 221201001865182038259832789)
            ·
              refine ⟨5184398481215204021714831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 221201001865182038259832789 5184398481215204021714831)
              ·
                refine ⟨7776597721822806032572247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5184398481215204021714831 7776597721822806032572247)
                ·
                  refine ⟨11664896582734209048858371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7776597721822806032572247 11664896582734209048858371)
                  ·
                    refine ⟨17497344874101313573287557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11664896582734209048858371 17497344874101313573287557)
                    ·
                      refine ⟨3280752163893996294991417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17497344874101313573287557 3280752163893996294991417)
                      ·
                        rfl

theorem cell23_6389242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7, 1, 1, 1, 4].length) (baseStart_6389242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6389242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6389242 prefixEnd_6389242 := by exact prefixLift 6389242
  have htrace : WordTrace (prefixWord ++ tailWord_6389242) baseStart_6389242 baseEnd_6389242 := by
    simpa [prefixWord, tailWord_6389242, baseEnd_6389242] using wordTrace_append hprefix tailTrace_6389242
  have hstable : (prefixWord ++ tailWord_6389242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6389242).length < 2 ^ (prefixWord ++ tailWord_6389242).sum := by decide
  have hdescent : baseEnd_6389242 < baseStart_6389242 := by decide
  rcases family_descends (prefixWord ++ tailWord_6389242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6389245 : List Nat := [1, 4, 1, 1, 1, 4, 3, 1, 1, 1, 5]
def baseStart_6389245 : Nat := 118140960795 + 6389245 * 2 ^ 59
def prefixEnd_6389245 : Nat := 4983230072969 + 3 ^ 40 * 6389245 * 2
def baseEnd_6389245 : Nat := 3280753704335959783253903

theorem tailTrace_6389245 : CollatzResearch.WordTrace tailWord_6389245 prefixEnd_6389245 3280753704335959783253903 := by
  unfold tailWord_6389245
  simp only [CollatzResearch.WordTrace]
  refine ⟨233034909737864036016545189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155356606491909357344363459 233034909737864036016545189)
  ·
    refine ⟨43694045575849506753102223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 233034909737864036016545189 43694045575849506753102223)
    ·
      refine ⟨65541068363774260129653335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43694045575849506753102223 65541068363774260129653335)
      ·
        refine ⟨98311602545661390194480003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65541068363774260129653335 98311602545661390194480003)
        ·
          refine ⟨147467403818492085291720005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98311602545661390194480003 147467403818492085291720005)
          ·
            refine ⟨27650138215967265992197501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 147467403818492085291720005 27650138215967265992197501)
            ·
              refine ⟨10368801830987724747074063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27650138215967265992197501 10368801830987724747074063)
              ·
                refine ⟨15553202746481587120611095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10368801830987724747074063 15553202746481587120611095)
                ·
                  refine ⟨23329804119722380680916643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15553202746481587120611095 23329804119722380680916643)
                  ·
                    refine ⟨34994706179583571021374965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23329804119722380680916643 34994706179583571021374965)
                    ·
                      refine ⟨3280753704335959783253903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34994706179583571021374965 3280753704335959783253903)
                      ·
                        rfl

theorem cell23_6389245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 1, 1, 1, 5].length) (baseStart_6389245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6389245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6389245 prefixEnd_6389245 := by exact prefixLift 6389245
  have htrace : WordTrace (prefixWord ++ tailWord_6389245) baseStart_6389245 baseEnd_6389245 := by
    simpa [prefixWord, tailWord_6389245, baseEnd_6389245] using wordTrace_append hprefix tailTrace_6389245
  have hstable : (prefixWord ++ tailWord_6389245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6389245).length < 2 ^ (prefixWord ++ tailWord_6389245).sum := by decide
  have hdescent : baseEnd_6389245 < baseStart_6389245 := by decide
  rcases family_descends (prefixWord ++ tailWord_6389245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6389272 : List Nat := [2, 1, 2, 3, 4, 1, 2, 1, 1, 2, 4]
def baseStart_6389272 : Nat := 118140960795 + 6389272 * 2 ^ 59
def prefixEnd_6389272 : Nat := 4983230072969 + 3 ^ 40 * 6389272 * 2
def baseEnd_6389272 : Nat := 3280767568313631177616279

theorem tailTrace_6389272 : CollatzResearch.WordTrace tailWord_6389272 prefixEnd_6389272 3280767568313631177616279 := by
  unfold tailWord_6389272
  simp only [CollatzResearch.WordTrace]
  refine ⟨116517947254383109813889035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155357263005844146418518713 116517947254383109813889035)
  ·
    refine ⟨174776920881574664720833553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116517947254383109813889035 174776920881574664720833553)
    ·
      refine ⟨131082690661180998540625165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174776920881574664720833553 131082690661180998540625165)
      ·
        refine ⟨49156008997942874452734437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131082690661180998540625165 49156008997942874452734437)
        ·
          refine ⟨9216751687114288959887707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49156008997942874452734437 9216751687114288959887707)
          ·
            refine ⟨13825127530671433439831561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9216751687114288959887707 13825127530671433439831561)
            ·
              refine ⟨10368845648003575079873671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13825127530671433439831561 10368845648003575079873671)
              ·
                refine ⟨15553268472005362619810507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10368845648003575079873671 15553268472005362619810507)
                ·
                  refine ⟨23329902708008043929715761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15553268472005362619810507 23329902708008043929715761)
                  ·
                    refine ⟨17497427031006032947286821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23329902708008043929715761 17497427031006032947286821)
                    ·
                      refine ⟨3280767568313631177616279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17497427031006032947286821 3280767568313631177616279)
                      ·
                        rfl

theorem cell23_6389272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_6389272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6389272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6389272 prefixEnd_6389272 := by exact prefixLift 6389272
  have htrace : WordTrace (prefixWord ++ tailWord_6389272) baseStart_6389272 baseEnd_6389272 := by
    simpa [prefixWord, tailWord_6389272, baseEnd_6389272] using wordTrace_append hprefix tailTrace_6389272
  have hstable : (prefixWord ++ tailWord_6389272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6389272).length < 2 ^ (prefixWord ++ tailWord_6389272).sum := by decide
  have hdescent : baseEnd_6389272 < baseStart_6389272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6389272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6389309 : List Nat := [1, 4, 1, 3, 3, 1, 1, 1, 4, 1, 3]
def baseStart_6389309 : Nat := 118140960795 + 6389309 * 2 ^ 59
def prefixEnd_6389309 : Nat := 4983230072969 + 3 ^ 40 * 6389309 * 2
def baseEnd_6389309 : Nat := 3280786567097847532853609

theorem tailTrace_6389309 : CollatzResearch.WordTrace tailWord_6389309 prefixEnd_6389309 3280786567097847532853609 := by
  unfold tailWord_6389309
  simp only [CollatzResearch.WordTrace]
  refine ⟨233037244009632174946874981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155358162673088116631249987 233037244009632174946874981)
  ·
    refine ⟨43694483251806032802539059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 233037244009632174946874981 43694483251806032802539059)
    ·
      refine ⟨65541724877709049203808589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43694483251806032802539059 65541724877709049203808589)
      ·
        refine ⟨24578146829140893451428221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65541724877709049203808589 24578146829140893451428221)
        ·
          refine ⟨9216805060927835044285583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24578146829140893451428221 9216805060927835044285583)
          ·
            refine ⟨13825207591391752566428375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9216805060927835044285583 13825207591391752566428375)
            ·
              refine ⟨20737811387087628849642563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13825207591391752566428375 20737811387087628849642563)
              ·
                refine ⟨31106717080631443274463845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20737811387087628849642563 31106717080631443274463845)
                ·
                  refine ⟨5832509452618395613961971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31106717080631443274463845 5832509452618395613961971)
                  ·
                    refine ⟨8748764178927593420942957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5832509452618395613961971 8748764178927593420942957)
                    ·
                      refine ⟨3280786567097847532853609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8748764178927593420942957 3280786567097847532853609)
                      ·
                        rfl

theorem cell23_6389309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_6389309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6389309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6389309 prefixEnd_6389309 := by exact prefixLift 6389309
  have htrace : WordTrace (prefixWord ++ tailWord_6389309) baseStart_6389309 baseEnd_6389309 := by
    simpa [prefixWord, tailWord_6389309, baseEnd_6389309] using wordTrace_append hprefix tailTrace_6389309
  have hstable : (prefixWord ++ tailWord_6389309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6389309).length < 2 ^ (prefixWord ++ tailWord_6389309).sum := by decide
  have hdescent : baseEnd_6389309 < baseStart_6389309 := by decide
  rcases family_descends (prefixWord ++ tailWord_6389309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6389315 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 2, 8, 2]
def baseStart_6389315 : Nat := 118140960795 + 6389315 * 2 ^ 59
def prefixEnd_6389315 : Nat := 4983230072969 + 3 ^ 40 * 6389315 * 2
def baseEnd_6389315 : Nat := 3280789647981774509378581

theorem tailTrace_6389315 : CollatzResearch.WordTrace tailWord_6389315 prefixEnd_6389315 3280789647981774509378581 := by
  unfold tailWord_6389315
  simp only [CollatzResearch.WordTrace]
  refine ⟨233037462847610437971593399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155358308565073625314395599 233037462847610437971593399)
  ·
    refine ⟨349556194271415656957390099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233037462847610437971593399 349556194271415656957390099)
    ·
      refine ⟨524334291407123485436085149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349556194271415656957390099 524334291407123485436085149)
      ·
        refine ⟨196625359277671307038531931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 524334291407123485436085149 196625359277671307038531931)
        ·
          refine ⟨294938038916506960557797897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196625359277671307038531931 294938038916506960557797897)
          ·
            refine ⟨221203529187380220418348423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 294938038916506960557797897 221203529187380220418348423)
            ·
              refine ⟨331805293781070330627522635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221203529187380220418348423 331805293781070330627522635)
              ·
                refine ⟨497707940671605495941283953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 331805293781070330627522635 497707940671605495941283953)
                ·
                  refine ⟨373280955503704121955962965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 497707940671605495941283953 373280955503704121955962965)
                  ·
                    refine ⟨4374386197309032679171441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 373280955503704121955962965 4374386197309032679171441)
                    ·
                      refine ⟨3280789647981774509378581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4374386197309032679171441 3280789647981774509378581)
                      ·
                        rfl

theorem cell23_6389315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 8, 2].length) (baseStart_6389315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6389315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6389315 prefixEnd_6389315 := by exact prefixLift 6389315
  have htrace : WordTrace (prefixWord ++ tailWord_6389315) baseStart_6389315 baseEnd_6389315 := by
    simpa [prefixWord, tailWord_6389315, baseEnd_6389315] using wordTrace_append hprefix tailTrace_6389315
  have hstable : (prefixWord ++ tailWord_6389315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6389315).length < 2 ^ (prefixWord ++ tailWord_6389315).sum := by decide
  have hdescent : baseEnd_6389315 < baseStart_6389315 := by decide
  rcases family_descends (prefixWord ++ tailWord_6389315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6389349 : List Nat := [1, 3, 1, 3, 3, 1, 1, 2, 4, 2, 2]
def baseStart_6389349 : Nat := 118140960795 + 6389349 * 2 ^ 59
def prefixEnd_6389349 : Nat := 4983230072969 + 3 ^ 40 * 6389349 * 2
def baseEnd_6389349 : Nat := 3280807106324027376353425

theorem tailTrace_6389349 : CollatzResearch.WordTrace tailWord_6389349 prefixEnd_6389349 3280807106324027376353425 := by
  unfold tailWord_6389349
  simp only [CollatzResearch.WordTrace]
  refine ⟨233038702929487261778331101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155359135286324841185554067 233038702929487261778331101)
  ·
    refine ⟨87389513598557723166874163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233038702929487261778331101 87389513598557723166874163)
    ·
      refine ⟨131084270397836584750311245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87389513598557723166874163 131084270397836584750311245)
      ·
        refine ⟨49156601399188719281366717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131084270397836584750311245 49156601399188719281366717)
        ·
          refine ⟨18433725524695769730512519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49156601399188719281366717 18433725524695769730512519)
          ·
            refine ⟨27650588287043654595768779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18433725524695769730512519 27650588287043654595768779)
            ·
              refine ⟨41475882430565481893653169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27650588287043654595768779 41475882430565481893653169)
              ·
                refine ⟨31106911822924111420239877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41475882430565481893653169 31106911822924111420239877)
                ·
                  refine ⟨5832545966798270891294977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31106911822924111420239877 5832545966798270891294977)
                  ·
                    refine ⟨4374409475098703168471233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5832545966798270891294977 4374409475098703168471233)
                    ·
                      refine ⟨3280807106324027376353425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4374409475098703168471233 3280807106324027376353425)
                      ·
                        rfl

theorem cell23_6389349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 4, 2, 2].length) (baseStart_6389349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6389349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6389349 prefixEnd_6389349 := by exact prefixLift 6389349
  have htrace : WordTrace (prefixWord ++ tailWord_6389349) baseStart_6389349 baseEnd_6389349 := by
    simpa [prefixWord, tailWord_6389349, baseEnd_6389349] using wordTrace_append hprefix tailTrace_6389349
  have hstable : (prefixWord ++ tailWord_6389349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6389349).length < 2 ^ (prefixWord ++ tailWord_6389349).sum := by decide
  have hdescent : baseEnd_6389349 < baseStart_6389349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6389349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6389352 : List Nat := [2, 1, 4, 3, 1, 2, 1, 1, 2, 1, 5]
def baseStart_6389352 : Nat := 118140960795 + 6389352 * 2 ^ 59
def prefixEnd_6389352 : Nat := 4983230072969 + 3 ^ 40 * 6389352 * 2
def baseEnd_6389352 : Nat := 3280808646765990864615911

theorem tailTrace_6389352 : CollatzResearch.WordTrace tailWord_6389352 prefixEnd_6389352 3280808646765990864615911 := by
  unfold tailWord_6389352
  simp only [CollatzResearch.WordTrace]
  refine ⟨116519406174238196645345155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155359208232317595527126873 116519406174238196645345155)
  ·
    refine ⟨174779109261357294968017733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116519406174238196645345155 174779109261357294968017733)
    ·
      refine ⟨32771082986504492806503325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 174779109261357294968017733 32771082986504492806503325)
      ·
        refine ⟨12289156119939184802438747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32771082986504492806503325 12289156119939184802438747)
        ·
          refine ⟨18433734179908777203658121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12289156119939184802438747 18433734179908777203658121)
          ·
            refine ⟨13825300634931582902743591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18433734179908777203658121 13825300634931582902743591)
            ·
              refine ⟨20737950952397374354115387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13825300634931582902743591 20737950952397374354115387)
              ·
                refine ⟨31106926428596061531173081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20737950952397374354115387 31106926428596061531173081)
                ·
                  refine ⟨23330194821447046148379811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31106926428596061531173081 23330194821447046148379811)
                  ·
                    refine ⟨34995292232170569222569717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23330194821447046148379811 34995292232170569222569717)
                    ·
                      refine ⟨3280808646765990864615911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34995292232170569222569717 3280808646765990864615911)
                      ·
                        rfl

theorem cell23_6389352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_6389352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6389352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6389352 prefixEnd_6389352 := by exact prefixLift 6389352
  have htrace : WordTrace (prefixWord ++ tailWord_6389352) baseStart_6389352 baseEnd_6389352 := by
    simpa [prefixWord, tailWord_6389352, baseEnd_6389352] using wordTrace_append hprefix tailTrace_6389352
  have hstable : (prefixWord ++ tailWord_6389352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6389352).length < 2 ^ (prefixWord ++ tailWord_6389352).sum := by decide
  have hdescent : baseEnd_6389352 < baseStart_6389352 := by decide
  rcases family_descends (prefixWord ++ tailWord_6389352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6389366 : List Nat := [5, 1, 1, 2, 2, 1, 2, 1, 4, 2, 2]
def baseStart_6389366 : Nat := 118140960795 + 6389366 * 2 ^ 59
def prefixEnd_6389366 : Nat := 4983230072969 + 3 ^ 40 * 6389366 * 2
def baseEnd_6389366 : Nat := 3280815835495153809840847

theorem tailTrace_6389366 : CollatzResearch.WordTrace tailWord_6389366 prefixEnd_6389366 3280815835495153809840847 := by
  unfold tailWord_6389366
  simp only [CollatzResearch.WordTrace]
  refine ⟨14564957685651604605106247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 155359548646950449121133301 14564957685651604605106247)
  ·
    refine ⟨21847436528477406907659371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14564957685651604605106247 21847436528477406907659371)
    ·
      refine ⟨32771154792716110361489057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21847436528477406907659371 32771154792716110361489057)
      ·
        refine ⟨24578366094537082771116793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32771154792716110361489057 24578366094537082771116793)
        ·
          refine ⟨18433774570902812078337595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24578366094537082771116793 18433774570902812078337595)
          ·
            refine ⟨27650661856354218117506393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18433774570902812078337595 27650661856354218117506393)
            ·
              refine ⟨20737996392265663588129795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27650661856354218117506393 20737996392265663588129795)
              ·
                refine ⟨31106994588398495382194693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20737996392265663588129795 31106994588398495382194693)
                ·
                  refine ⟨5832561485324717884161505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31106994588398495382194693 5832561485324717884161505)
                  ·
                    refine ⟨4374421113993538413121129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5832561485324717884161505 4374421113993538413121129)
                    ·
                      refine ⟨3280815835495153809840847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4374421113993538413121129 3280815835495153809840847)
                      ·
                        rfl

theorem cell23_6389366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_6389366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6389366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6389366 prefixEnd_6389366 := by exact prefixLift 6389366
  have htrace : WordTrace (prefixWord ++ tailWord_6389366) baseStart_6389366 baseEnd_6389366 := by
    simpa [prefixWord, tailWord_6389366, baseEnd_6389366] using wordTrace_append hprefix tailTrace_6389366
  have hstable : (prefixWord ++ tailWord_6389366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6389366).length < 2 ^ (prefixWord ++ tailWord_6389366).sum := by decide
  have hdescent : baseEnd_6389366 < baseStart_6389366 := by decide
  rcases family_descends (prefixWord ++ tailWord_6389366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6389383 : List Nat := [1, 1, 4, 2, 1, 5, 2, 1, 2, 2, 2]
def baseStart_6389383 : Nat := 118140960795 + 6389383 * 2 ^ 59
def prefixEnd_6389383 : Nat := 4983230072969 + 3 ^ 40 * 6389383 * 2
def baseEnd_6389383 : Nat := 3280824564666280243328269

theorem tailTrace_6389383 : CollatzResearch.WordTrace tailWord_6389383 prefixEnd_6389383 3280824564666280243328269 := by
  unfold tailWord_6389383
  simp only [CollatzResearch.WordTrace]
  refine ⟨233039943011364085585068803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155359962007576057056712535 233039943011364085585068803)
  ·
    refine ⟨349559914517046128377603205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233039943011364085585068803 349559914517046128377603205)
    ·
      refine ⟨65542483971946149070800601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 349559914517046128377603205 65542483971946149070800601)
      ·
        refine ⟨49156862978959611803100451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65542483971946149070800601 49156862978959611803100451)
        ·
          refine ⟨73735294468439417704650677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49156862978959611803100451 73735294468439417704650677)
          ·
            refine ⟨6912683856416195409811001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73735294468439417704650677 6912683856416195409811001)
            ·
              refine ⟨5184512892312146557358251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6912683856416195409811001 5184512892312146557358251)
              ·
                refine ⟨7776769338468219836037377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5184512892312146557358251 7776769338468219836037377)
                ·
                  refine ⟨5832577003851164877028033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7776769338468219836037377 5832577003851164877028033)
                  ·
                    refine ⟨4374432752888373657771025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5832577003851164877028033 4374432752888373657771025)
                    ·
                      refine ⟨3280824564666280243328269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4374432752888373657771025 3280824564666280243328269)
                      ·
                        rfl

theorem cell23_6389383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2, 1, 2, 2, 2].length) (baseStart_6389383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6389383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6389383 prefixEnd_6389383 := by exact prefixLift 6389383
  have htrace : WordTrace (prefixWord ++ tailWord_6389383) baseStart_6389383 baseEnd_6389383 := by
    simpa [prefixWord, tailWord_6389383, baseEnd_6389383] using wordTrace_append hprefix tailTrace_6389383
  have hstable : (prefixWord ++ tailWord_6389383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6389383).length < 2 ^ (prefixWord ++ tailWord_6389383).sum := by decide
  have hdescent : baseEnd_6389383 < baseStart_6389383 := by decide
  rcases family_descends (prefixWord ++ tailWord_6389383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6389466 : List Nat := [3, 1, 1, 2, 2, 4, 2, 3, 1, 4]
def baseStart_6389466 : Nat := 118140960795 + 6389466 * 2 ^ 59
def prefixEnd_6389466 : Nat := 4983230072969 + 3 ^ 40 * 6389466 * 2
def baseEnd_6389466 : Nat := 1093622394520201139530129

theorem tailTrace_6389466 : CollatzResearch.WordTrace tailWord_6389466 prefixEnd_6389466 1093622394520201139530129 := by
  unfold tailWord_6389466
  simp only [CollatzResearch.WordTrace]
  refine ⟨58260742567515847690085063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155361980180042260506893501 58260742567515847690085063)
  ·
    refine ⟨87391113851273771535127595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58260742567515847690085063 87391113851273771535127595)
    ·
      refine ⟨131086670776910657302691393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87391113851273771535127595 131086670776910657302691393)
      ·
        refine ⟨98315003082682992977018545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131086670776910657302691393 98315003082682992977018545)
        ·
          refine ⟨73736252312012244732763909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98315003082682992977018545 73736252312012244732763909)
          ·
            refine ⟨13825547308502295887393233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73736252312012244732763909 13825547308502295887393233)
            ·
              refine ⟨10369160481376721915544925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13825547308502295887393233 10369160481376721915544925)
              ·
                refine ⟨3888435180516270718329347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10369160481376721915544925 3888435180516270718329347)
                ·
                  refine ⟨5832652770774406077494021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3888435180516270718329347 5832652770774406077494021)
                  ·
                    refine ⟨1093622394520201139530129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5832652770774406077494021 1093622394520201139530129)
                    ·
                      rfl

theorem cell23_6389466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 3, 1, 4].length) (baseStart_6389466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6389466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6389466 prefixEnd_6389466 := by exact prefixLift 6389466
  have htrace : WordTrace (prefixWord ++ tailWord_6389466) baseStart_6389466 baseEnd_6389466 := by
    simpa [prefixWord, tailWord_6389466, baseEnd_6389466] using wordTrace_append hprefix tailTrace_6389466
  have hstable : (prefixWord ++ tailWord_6389466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6389466).length < 2 ^ (prefixWord ++ tailWord_6389466).sum := by decide
  have hdescent : baseEnd_6389466 < baseStart_6389466 := by decide
  rcases family_descends (prefixWord ++ tailWord_6389466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6389479 : List Nat := [1, 1, 5, 4, 1, 1, 1, 1, 8]
def baseStart_6389479 : Nat := 118140960795 + 6389479 * 2 ^ 59
def prefixEnd_6389479 : Nat := 4983230072969 + 3 ^ 40 * 6389479 * 2
def baseEnd_6389479 : Nat := 364541539867679096414203

theorem tailTrace_6389479 : CollatzResearch.WordTrace tailWord_6389479 prefixEnd_6389479 364541539867679096414203 := by
  unfold tailWord_6389479
  simp only [CollatzResearch.WordTrace]
  refine ⟨233043444419016293980563491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155362296279344195987042327 233043444419016293980563491)
  ·
    refine ⟨349565166628524440970845237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233043444419016293980563491 349565166628524440970845237)
    ·
      refine ⟨32771734371424166341016741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 349565166628524440970845237 32771734371424166341016741)
      ·
        refine ⟨6144700194642031188940639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32771734371424166341016741 6144700194642031188940639)
        ·
          refine ⟨9217050291963046783410959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6144700194642031188940639 9217050291963046783410959)
          ·
            refine ⟨13825575437944570175116439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9217050291963046783410959 13825575437944570175116439)
            ·
              refine ⟨20738363156916855262674659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13825575437944570175116439 20738363156916855262674659)
              ·
                refine ⟨31107544735375282894011989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20738363156916855262674659 31107544735375282894011989)
                ·
                  refine ⟨364541539867679096414203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31107544735375282894011989 364541539867679096414203)
                  ·
                    rfl

theorem cell23_6389479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 8].length) (baseStart_6389479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6389479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6389479 prefixEnd_6389479 := by exact prefixLift 6389479
  have htrace : WordTrace (prefixWord ++ tailWord_6389479) baseStart_6389479 baseEnd_6389479 := by
    simpa [prefixWord, tailWord_6389479, baseEnd_6389479] using wordTrace_append hprefix tailTrace_6389479
  have hstable : (prefixWord ++ tailWord_6389479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6389479).length < 2 ^ (prefixWord ++ tailWord_6389479).sum := by decide
  have hdescent : baseEnd_6389479 < baseStart_6389479 := by decide
  rcases family_descends (prefixWord ++ tailWord_6389479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6389489 : List Nat := [1, 2, 2, 2, 2, 3, 1, 3, 3, 1, 3]
def baseStart_6389489 : Nat := 118140960795 + 6389489 * 2 ^ 59
def prefixEnd_6389489 : Nat := 4983230072969 + 3 ^ 40 * 6389489 * 2
def baseEnd_6389489 : Nat := 3280878993615656828602781

theorem tailTrace_6389489 : CollatzResearch.WordTrace tailWord_6389489 prefixEnd_6389489 3280878993615656828602781 := by
  unfold tailWord_6389489
  simp only [CollatzResearch.WordTrace]
  refine ⟨233043809148980065688427521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155362539432653377125618347 233043809148980065688427521)
  ·
    refine ⟨174782856861735049266320641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233043809148980065688427521 174782856861735049266320641)
    ·
      refine ⟨131087142646301286949740481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174782856861735049266320641 131087142646301286949740481)
      ·
        refine ⟨98315356984725965212305361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131087142646301286949740481 98315356984725965212305361)
        ·
          refine ⟨73736517738544473909229021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98315356984725965212305361 73736517738544473909229021)
          ·
            refine ⟨27651194151954177715960883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73736517738544473909229021 27651194151954177715960883)
            ·
              refine ⟨41476791227931266573941325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27651194151954177715960883 41476791227931266573941325)
              ·
                refine ⟨15553796710474224965227997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41476791227931266573941325 15553796710474224965227997)
                ·
                  refine ⟨5832673766427834361960499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15553796710474224965227997 5832673766427834361960499)
                  ·
                    refine ⟨8749010649641751542940749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5832673766427834361960499 8749010649641751542940749)
                    ·
                      refine ⟨3280878993615656828602781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8749010649641751542940749 3280878993615656828602781)
                      ·
                        rfl

theorem cell23_6389489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 3, 3, 1, 3].length) (baseStart_6389489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6389489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6389489 prefixEnd_6389489 := by exact prefixLift 6389489
  have htrace : WordTrace (prefixWord ++ tailWord_6389489) baseStart_6389489 baseEnd_6389489 := by
    simpa [prefixWord, tailWord_6389489, baseEnd_6389489] using wordTrace_append hprefix tailTrace_6389489
  have hstable : (prefixWord ++ tailWord_6389489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6389489).length < 2 ^ (prefixWord ++ tailWord_6389489).sum := by decide
  have hdescent : baseEnd_6389489 < baseStart_6389489 := by decide
  rcases family_descends (prefixWord ++ tailWord_6389489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6389506 : List Nat := [3, 4, 1, 1, 1, 1, 1, 4, 3, 1, 3]
def baseStart_6389506 : Nat := 118140960795 + 6389506 * 2 ^ 59
def prefixEnd_6389506 : Nat := 4983230072969 + 3 ^ 40 * 6389506 * 2
def baseEnd_6389506 : Nat := 3280887722786783262090203

theorem tailTrace_6389506 : CollatzResearch.WordTrace tailWord_6389506 prefixEnd_6389506 3280887722786783262090203 := by
  unfold tailWord_6389506
  simp only [CollatzResearch.WordTrace]
  refine ⟨58261107297479619397949093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155362952793278985061197581 58261107297479619397949093)
  ·
    refine ⟨10923957618277428637115455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58261107297479619397949093 10923957618277428637115455)
    ·
      refine ⟨16385936427416142955673183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10923957618277428637115455 16385936427416142955673183)
      ·
        refine ⟨24578904641124214433509775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16385936427416142955673183 24578904641124214433509775)
        ·
          refine ⟨36868356961686321650264663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24578904641124214433509775 36868356961686321650264663)
          ·
            refine ⟨55302535442529482475396995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36868356961686321650264663 55302535442529482475396995)
            ·
              refine ⟨82953803163794223713095493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55302535442529482475396995 82953803163794223713095493)
              ·
                refine ⟨15553838093211416946205405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82953803163794223713095493 15553838093211416946205405)
                ·
                  refine ⟨5832689284954281354827027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15553838093211416946205405 5832689284954281354827027)
                  ·
                    refine ⟨8749033927431422032240541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5832689284954281354827027 8749033927431422032240541)
                    ·
                      refine ⟨3280887722786783262090203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8749033927431422032240541 3280887722786783262090203)
                      ·
                        rfl

theorem cell23_6389506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_6389506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6389506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6389506 prefixEnd_6389506 := by exact prefixLift 6389506
  have htrace : WordTrace (prefixWord ++ tailWord_6389506) baseStart_6389506 baseEnd_6389506 := by
    simpa [prefixWord, tailWord_6389506, baseEnd_6389506] using wordTrace_append hprefix tailTrace_6389506
  have hstable : (prefixWord ++ tailWord_6389506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6389506).length < 2 ^ (prefixWord ++ tailWord_6389506).sum := by decide
  have hdescent : baseEnd_6389506 < baseStart_6389506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6389506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6389540 : List Nat := [2, 3, 1, 3, 2, 2, 3, 2, 1, 1, 3]
def baseStart_6389540 : Nat := 118140960795 + 6389540 * 2 ^ 59
def prefixEnd_6389540 : Nat := 4983230072969 + 3 ^ 40 * 6389540 * 2
def baseEnd_6389540 : Nat := 3280905181129036129065047

theorem tailTrace_6389540 : CollatzResearch.WordTrace tailWord_6389540 prefixEnd_6389540 3280905181129036129065047 := by
  unfold tailWord_6389540
  simp only [CollatzResearch.WordTrace]
  refine ⟨116522834635897650699267037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155363779514530200932356049 116522834635897650699267037)
  ·
    refine ⟨43696062988461619012225139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116522834635897650699267037 43696062988461619012225139)
    ·
      refine ⟨65544094482692428518337709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43696062988461619012225139 65544094482692428518337709)
      ·
        refine ⟨24579035431009660694376641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65544094482692428518337709 24579035431009660694376641)
        ·
          refine ⟨18434276573257245520782481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24579035431009660694376641 18434276573257245520782481)
          ·
            refine ⟨13825707429942934140586861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18434276573257245520782481 13825707429942934140586861)
            ·
              refine ⟨5184640286228600302720073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13825707429942934140586861 5184640286228600302720073)
              ·
                refine ⟨3888480214671450227040055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5184640286228600302720073 3888480214671450227040055)
                ·
                  refine ⟨5832720322007175340560083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3888480214671450227040055 5832720322007175340560083)
                  ·
                    refine ⟨8749080483010763010840125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5832720322007175340560083 8749080483010763010840125)
                    ·
                      refine ⟨3280905181129036129065047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8749080483010763010840125 3280905181129036129065047)
                      ·
                        rfl

theorem cell23_6389540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_6389540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6389540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6389540 prefixEnd_6389540 := by exact prefixLift 6389540
  have htrace : WordTrace (prefixWord ++ tailWord_6389540) baseStart_6389540 baseEnd_6389540 := by
    simpa [prefixWord, tailWord_6389540, baseEnd_6389540] using wordTrace_append hprefix tailTrace_6389540
  have hstable : (prefixWord ++ tailWord_6389540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6389540).length < 2 ^ (prefixWord ++ tailWord_6389540).sum := by decide
  have hdescent : baseEnd_6389540 < baseStart_6389540 := by decide
  rcases family_descends (prefixWord ++ tailWord_6389540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6389545 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 1, 4, 7]
def baseStart_6389545 : Nat := 118140960795 + 6389545 * 2 ^ 59
def prefixEnd_6389545 : Nat := 4983230072969 + 3 ^ 40 * 6389545 * 2
def baseEnd_6389545 : Nat := 3280907748532308609502523

theorem tailTrace_6389545 : CollatzResearch.WordTrace tailWord_6389545 prefixEnd_6389545 3280907748532308609502523 := by
  unfold tailWord_6389545
  simp only [CollatzResearch.WordTrace]
  refine ⟨233045851636777187252466089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155363901091184791501644059 233045851636777187252466089)
  ·
    refine ⟨174784388727582890439349567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233045851636777187252466089 174784388727582890439349567)
    ·
      refine ⟨262176583091374335659024351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174784388727582890439349567 262176583091374335659024351)
      ·
        refine ⟨393264874637061503488536527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262176583091374335659024351 393264874637061503488536527)
        ·
          refine ⟨589897311955592255232804791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 393264874637061503488536527 589897311955592255232804791)
          ·
            refine ⟨884845967933388382849207187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 589897311955592255232804791 884845967933388382849207187)
            ·
              refine ⟨1327268951900082574273810781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 884845967933388382849207187 1327268951900082574273810781)
              ·
                refine ⟨497725856962530965352679043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1327268951900082574273810781 497725856962530965352679043)
                ·
                  refine ⟨746588785443796448029018565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 497725856962530965352679043 746588785443796448029018565)
                  ·
                    refine ⟨139985397270711834005440981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 746588785443796448029018565 139985397270711834005440981)
                    ·
                      refine ⟨3280907748532308609502523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 139985397270711834005440981 3280907748532308609502523)
                      ·
                        rfl

theorem cell23_6389545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 4, 7].length) (baseStart_6389545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6389545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6389545 prefixEnd_6389545 := by exact prefixLift 6389545
  have htrace : WordTrace (prefixWord ++ tailWord_6389545) baseStart_6389545 baseEnd_6389545 := by
    simpa [prefixWord, tailWord_6389545, baseEnd_6389545] using wordTrace_append hprefix tailTrace_6389545
  have hstable : (prefixWord ++ tailWord_6389545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6389545).length < 2 ^ (prefixWord ++ tailWord_6389545).sum := by decide
  have hdescent : baseEnd_6389545 < baseStart_6389545 := by decide
  rcases family_descends (prefixWord ++ tailWord_6389545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6389566 : List Nat := [4, 2, 1, 2, 2, 2, 1, 1, 3, 2, 3]
def baseStart_6389566 : Nat := 118140960795 + 6389566 * 2 ^ 59
def prefixEnd_6389566 : Nat := 4983230072969 + 3 ^ 40 * 6389566 * 2
def baseEnd_6389566 : Nat := 3280918531626053027339927

theorem tailTrace_6389566 : CollatzResearch.WordTrace tailWord_6389566 prefixEnd_6389566 3280918531626053027339927 := by
  unfold tailWord_6389566
  simp only [CollatzResearch.WordTrace]
  refine ⟨29130827196212638479872569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155364411713134071892653701 29130827196212638479872569)
  ·
    refine ⟨21848120397159478859904427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29130827196212638479872569 21848120397159478859904427)
    ·
      refine ⟨32772180595739218289856641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21848120397159478859904427 32772180595739218289856641)
      ·
        refine ⟨24579135446804413717392481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32772180595739218289856641 24579135446804413717392481)
        ·
          refine ⟨18434351585103310288044361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24579135446804413717392481 18434351585103310288044361)
          ·
            refine ⟨13825763688827482716033271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18434351585103310288044361 13825763688827482716033271)
            ·
              refine ⟨20738645533241224074049907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13825763688827482716033271 20738645533241224074049907)
              ·
                refine ⟨31107968299861836111074861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20738645533241224074049907 31107968299861836111074861)
                ·
                  refine ⟨11665488112448188541653073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31107968299861836111074861 11665488112448188541653073)
                  ·
                    refine ⟨8749116084336141406239805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11665488112448188541653073 8749116084336141406239805)
                    ·
                      refine ⟨3280918531626053027339927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8749116084336141406239805 3280918531626053027339927)
                      ·
                        rfl

theorem cell23_6389566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_6389566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6389566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6389566 prefixEnd_6389566 := by exact prefixLift 6389566
  have htrace : WordTrace (prefixWord ++ tailWord_6389566) baseStart_6389566 baseEnd_6389566 := by
    simpa [prefixWord, tailWord_6389566, baseEnd_6389566] using wordTrace_append hprefix tailTrace_6389566
  have hstable : (prefixWord ++ tailWord_6389566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6389566).length < 2 ^ (prefixWord ++ tailWord_6389566).sum := by decide
  have hdescent : baseEnd_6389566 < baseStart_6389566 := by decide
  rcases family_descends (prefixWord ++ tailWord_6389566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6389612 : List Nat := [2, 2, 1, 1, 4, 2, 1, 1, 1, 8]
def baseStart_6389612 : Nat := 118140960795 + 6389612 * 2 ^ 59
def prefixEnd_6389612 : Nat := 4983230072969 + 3 ^ 40 * 6389612 * 2
def baseEnd_6389612 : Nat := 1093647383912053282454905

theorem tailTrace_6389612 : CollatzResearch.WordTrace tailWord_6389612 prefixEnd_6389612 1093647383912053282454905 := by
  unfold tailWord_6389612
  simp only [CollatzResearch.WordTrace]
  refine ⟨116524147663767228847577545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155365530218356305130103393 116524147663767228847577545)
  ·
    refine ⟨87393110747825421635683159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116524147663767228847577545 87393110747825421635683159)
    ·
      refine ⟨131089666121738132453524739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87393110747825421635683159 131089666121738132453524739)
      ·
        refine ⟨196634499182607198680287109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131089666121738132453524739 196634499182607198680287109)
        ·
          refine ⟨36868968596738849752553833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 196634499182607198680287109 36868968596738849752553833)
          ·
            refine ⟨27651726447554137314415375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36868968596738849752553833 27651726447554137314415375)
            ·
              refine ⟨41477589671331205971623063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27651726447554137314415375 41477589671331205971623063)
              ·
                refine ⟨62216384506996808957434595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41477589671331205971623063 62216384506996808957434595)
                ·
                  refine ⟨93324576760495213436151893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62216384506996808957434595 93324576760495213436151893)
                  ·
                    refine ⟨1093647383912053282454905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 93324576760495213436151893 1093647383912053282454905)
                    ·
                      rfl

theorem cell23_6389612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 8].length) (baseStart_6389612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6389612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6389612 prefixEnd_6389612 := by exact prefixLift 6389612
  have htrace : WordTrace (prefixWord ++ tailWord_6389612) baseStart_6389612 baseEnd_6389612 := by
    simpa [prefixWord, tailWord_6389612, baseEnd_6389612] using wordTrace_append hprefix tailTrace_6389612
  have hstable : (prefixWord ++ tailWord_6389612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6389612).length < 2 ^ (prefixWord ++ tailWord_6389612).sum := by decide
  have hdescent : baseEnd_6389612 < baseStart_6389612 := by decide
  rcases family_descends (prefixWord ++ tailWord_6389612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6389632 : List Nat := [2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 4]
def baseStart_6389632 : Nat := 118140960795 + 6389632 * 2 ^ 59
def prefixEnd_6389632 : Nat := 4983230072969 + 3 ^ 40 * 6389632 * 2
def baseEnd_6389632 : Nat := 3280952421349249769114623

theorem tailTrace_6389632 : CollatzResearch.WordTrace tailWord_6389632 prefixEnd_6389632 3280952421349249769114623 := by
  unfold tailWord_6389632
  simp only [CollatzResearch.WordTrace]
  refine ⟨116524512393731000555441575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155366016524974667407255433 116524512393731000555441575)
  ·
    refine ⟨174786768590596500833162363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116524512393731000555441575 174786768590596500833162363)
    ·
      refine ⟨262180152885894751249743545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174786768590596500833162363 262180152885894751249743545)
      ·
        refine ⟨196635114664421063437307659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262180152885894751249743545 196635114664421063437307659)
        ·
          refine ⟨294952671996631595155961489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196635114664421063437307659 294952671996631595155961489)
          ·
            refine ⟨221214503997473696366971117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 294952671996631595155961489 221214503997473696366971117)
            ·
              refine ⟨82955438999052636137614169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 221214503997473696366971117 82955438999052636137614169)
              ·
                refine ⟨62216579249289477103210627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82955438999052636137614169 62216579249289477103210627)
                ·
                  refine ⟨93324868873934215654815941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62216579249289477103210627 93324868873934215654815941)
                  ·
                    refine ⟨17498412913862665435277989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 93324868873934215654815941 17498412913862665435277989)
                    ·
                      refine ⟨3280952421349249769114623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17498412913862665435277989 3280952421349249769114623)
                      ·
                        rfl

theorem cell23_6389632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 4].length) (baseStart_6389632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6389632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6389632 prefixEnd_6389632 := by exact prefixLift 6389632
  have htrace : WordTrace (prefixWord ++ tailWord_6389632) baseStart_6389632 baseEnd_6389632 := by
    simpa [prefixWord, tailWord_6389632, baseEnd_6389632] using wordTrace_append hprefix tailTrace_6389632
  have hstable : (prefixWord ++ tailWord_6389632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6389632).length < 2 ^ (prefixWord ++ tailWord_6389632).sum := by decide
  have hdescent : baseEnd_6389632 < baseStart_6389632 := by decide
  rcases family_descends (prefixWord ++ tailWord_6389632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6389636 : List Nat := [2, 3, 2, 1, 1, 1, 4, 2, 1, 4, 2]
def baseStart_6389636 : Nat := 118140960795 + 6389636 * 2 ^ 59
def prefixEnd_6389636 : Nat := 4983230072969 + 3 ^ 40 * 6389636 * 2
def baseEnd_6389636 : Nat := 3280954475271867753464605

theorem tailTrace_6389636 : CollatzResearch.WordTrace tailWord_6389636 prefixEnd_6389636 3280954475271867753464605 := by
  unfold tailWord_6389636
  simp only [CollatzResearch.WordTrace]
  refine ⟨116524585339723754897014381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155366113786298339862685841 116524585339723754897014381)
  ·
    refine ⟨43696719502396408086380393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116524585339723754897014381 43696719502396408086380393)
    ·
      refine ⟨32772539626797306064785295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43696719502396408086380393 32772539626797306064785295)
      ·
        refine ⟨49158809440195959097177943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32772539626797306064785295 49158809440195959097177943)
        ·
          refine ⟨73738214160293938645766915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49158809440195959097177943 73738214160293938645766915)
          ·
            refine ⟨110607321240440907968650373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73738214160293938645766915 110607321240440907968650373)
            ·
              refine ⟨20738872732582670244121945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110607321240440907968650373 20738872732582670244121945)
              ·
                refine ⟨15554154549437002683091459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20738872732582670244121945 15554154549437002683091459)
                ·
                  refine ⟨23331231824155504024637189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15554154549437002683091459 23331231824155504024637189)
                  ·
                    refine ⟨4374605967029157004619473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23331231824155504024637189 4374605967029157004619473)
                    ·
                      refine ⟨3280954475271867753464605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4374605967029157004619473 3280954475271867753464605)
                      ·
                        rfl

theorem cell23_6389636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 2, 1, 4, 2].length) (baseStart_6389636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6389636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6389636 prefixEnd_6389636 := by exact prefixLift 6389636
  have htrace : WordTrace (prefixWord ++ tailWord_6389636) baseStart_6389636 baseEnd_6389636 := by
    simpa [prefixWord, tailWord_6389636, baseEnd_6389636] using wordTrace_append hprefix tailTrace_6389636
  have hstable : (prefixWord ++ tailWord_6389636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6389636).length < 2 ^ (prefixWord ++ tailWord_6389636).sum := by decide
  have hdescent : baseEnd_6389636 < baseStart_6389636 := by decide
  rcases family_descends (prefixWord ++ tailWord_6389636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6389689 : List Nat := [1, 2, 1, 4, 2, 1, 2, 3, 2, 5]
def baseStart_6389689 : Nat := 118140960795 + 6389689 * 2 ^ 59
def prefixEnd_6389689 : Nat := 4983230072969 + 3 ^ 40 * 6389689 * 2
def baseEnd_6389689 : Nat := 1093660563248852015367287

theorem tailTrace_6389689 : CollatzResearch.WordTrace tailWord_6389689 prefixEnd_6389689 1093660563248852015367287 := by
  unfold tailWord_6389689
  simp only [CollatzResearch.WordTrace]
  refine ⟨233051103748255499845708121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155367402498836999897138747 233051103748255499845708121)
  ·
    refine ⟨174788327811191624884281091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233051103748255499845708121 174788327811191624884281091)
    ·
      refine ⟨262182491716787437326421637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174788327811191624884281091 262182491716787437326421637)
      ·
        refine ⟨49159217196897644498704057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 262182491716787437326421637 49159217196897644498704057)
        ·
          refine ⟨36869412897673233374028043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49159217196897644498704057 36869412897673233374028043)
          ·
            refine ⟨55304119346509850061042065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36869412897673233374028043 55304119346509850061042065)
            ·
              refine ⟨41478089509882387545781549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55304119346509850061042065 41478089509882387545781549)
              ·
                refine ⟨15554283566205895329668081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41478089509882387545781549 15554283566205895329668081)
                ·
                  refine ⟨11665712674654421497251061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15554283566205895329668081 11665712674654421497251061)
                  ·
                    refine ⟨1093660563248852015367287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11665712674654421497251061 1093660563248852015367287)
                    ·
                      rfl

theorem cell23_6389689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 3, 2, 5].length) (baseStart_6389689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6389689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6389689 prefixEnd_6389689 := by exact prefixLift 6389689
  have htrace : WordTrace (prefixWord ++ tailWord_6389689) baseStart_6389689 baseEnd_6389689 := by
    simpa [prefixWord, tailWord_6389689, baseEnd_6389689] using wordTrace_append hprefix tailTrace_6389689
  have hstable : (prefixWord ++ tailWord_6389689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6389689).length < 2 ^ (prefixWord ++ tailWord_6389689).sum := by decide
  have hdescent : baseEnd_6389689 < baseStart_6389689 := by decide
  rcases family_descends (prefixWord ++ tailWord_6389689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6389693 : List Nat := [1, 4, 1, 2, 3, 3, 1, 3, 5]
def baseStart_6389693 : Nat := 118140960795 + 6389693 * 2 ^ 59
def prefixEnd_6389693 : Nat := 4983230072969 + 3 ^ 40 * 6389693 * 2
def baseEnd_6389693 : Nat := 364553749296574892272427

theorem tailTrace_6389693 : CollatzResearch.WordTrace tailWord_6389693 prefixEnd_6389693 364553749296574892272427 := by
  unfold tailWord_6389693
  simp only [CollatzResearch.WordTrace]
  refine ⟨233051249640241008528853733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155367499760160672352569155 233051249640241008528853733)
  ·
    refine ⟨43697109307545189099160075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 233051249640241008528853733 43697109307545189099160075)
    ·
      refine ⟨65545663961317783648740113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43697109307545189099160075 65545663961317783648740113)
      ·
        refine ⟨49159247970988337736555085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65545663961317783648740113 49159247970988337736555085)
        ·
          refine ⟨18434717989120626651208157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49159247970988337736555085 18434717989120626651208157)
          ·
            refine ⟨6913019245920234994203059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18434717989120626651208157 6913019245920234994203059)
            ·
              refine ⟨10369528868880352491304589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6913019245920234994203059 10369528868880352491304589)
              ·
                refine ⟨3888573325830132184239221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10369528868880352491304589 3888573325830132184239221)
                ·
                  refine ⟨364553749296574892272427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3888573325830132184239221 364553749296574892272427)
                  ·
                    rfl

theorem cell23_6389693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 3, 5].length) (baseStart_6389693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6389693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6389693 prefixEnd_6389693 := by exact prefixLift 6389693
  have htrace : WordTrace (prefixWord ++ tailWord_6389693) baseStart_6389693 baseEnd_6389693 := by
    simpa [prefixWord, tailWord_6389693, baseEnd_6389693] using wordTrace_append hprefix tailTrace_6389693
  have hstable : (prefixWord ++ tailWord_6389693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6389693).length < 2 ^ (prefixWord ++ tailWord_6389693).sum := by decide
  have hdescent : baseEnd_6389693 < baseStart_6389693 := by decide
  rcases family_descends (prefixWord ++ tailWord_6389693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6389729 : List Nat := [1, 2, 3, 1, 2, 1, 2, 1, 3, 4, 3]
def baseStart_6389729 : Nat := 118140960795 + 6389729 * 2 ^ 59
def prefixEnd_6389729 : Nat := 4983230072969 + 3 ^ 40 * 6389729 * 2
def baseEnd_6389729 : Nat := 3281002228972735889601677

theorem tailTrace_6389729 : CollatzResearch.WordTrace tailWord_6389729 prefixEnd_6389729 3281002228972735889601677 := by
  unfold tailWord_6389729
  simp only [CollatzResearch.WordTrace]
  refine ⟨233052562668110586677164241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155368375112073724451442827 233052562668110586677164241)
  ·
    refine ⟨174789422001082940007873181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233052562668110586677164241 174789422001082940007873181)
    ·
      refine ⟨65546033250406102502952443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174789422001082940007873181 65546033250406102502952443)
      ·
        refine ⟨98319049875609153754428665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65546033250406102502952443 98319049875609153754428665)
        ·
          refine ⟨73739287406706865315821499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98319049875609153754428665 73739287406706865315821499)
          ·
            refine ⟨110608931110060297973732249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73739287406706865315821499 110608931110060297973732249)
            ·
              refine ⟨82956698332545223480299187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110608931110060297973732249 82956698332545223480299187)
              ·
                refine ⟨124435047498817835220448781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82956698332545223480299187 124435047498817835220448781)
                ·
                  refine ⟨46663142812056688207668293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 124435047498817835220448781 46663142812056688207668293)
                  ·
                    refine ⟨8749339277260629038937805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46663142812056688207668293 8749339277260629038937805)
                    ·
                      refine ⟨3281002228972735889601677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8749339277260629038937805 3281002228972735889601677)
                      ·
                        rfl

theorem cell23_6389729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 4, 3].length) (baseStart_6389729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6389729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6389729 prefixEnd_6389729 := by exact prefixLift 6389729
  have htrace : WordTrace (prefixWord ++ tailWord_6389729) baseStart_6389729 baseEnd_6389729 := by
    simpa [prefixWord, tailWord_6389729, baseEnd_6389729] using wordTrace_append hprefix tailTrace_6389729
  have hstable : (prefixWord ++ tailWord_6389729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6389729).length < 2 ^ (prefixWord ++ tailWord_6389729).sum := by decide
  have hdescent : baseEnd_6389729 < baseStart_6389729 := by decide
  rcases family_descends (prefixWord ++ tailWord_6389729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6389770 : List Nat := [3, 1, 2, 2, 4, 1, 1, 4, 1, 4]
def baseStart_6389770 : Nat := 118140960795 + 6389770 * 2 ^ 59
def prefixEnd_6389770 : Nat := 4983230072969 + 3 ^ 40 * 6389770 * 2
def baseEnd_6389770 : Nat := 1093674427226523409729663

theorem tailTrace_6389770 : CollatzResearch.WordTrace tailWord_6389770 prefixEnd_6389770 1093674427226523409729663 := by
  unfold tailWord_6389770
  simp only [CollatzResearch.WordTrace]
  refine ⟨58263514515240512669851691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155369372040641367119604509 58263514515240512669851691)
  ·
    refine ⟨87395271772860769004777537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58263514515240512669851691 87395271772860769004777537)
    ·
      refine ⟨65546453829645576753583153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87395271772860769004777537 65546453829645576753583153)
      ·
        refine ⟨49159840372234182565187365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65546453829645576753583153 49159840372234182565187365)
        ·
          refine ⟨9217470069793909230972631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49159840372234182565187365 9217470069793909230972631)
          ·
            refine ⟨13826205104690863846458947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9217470069793909230972631 13826205104690863846458947)
            ·
              refine ⟨20739307657036295769688421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13826205104690863846458947 20739307657036295769688421)
              ·
                refine ⟨3888620185694305456816579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20739307657036295769688421 3888620185694305456816579)
                ·
                  refine ⟨5832930278541458185224869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3888620185694305456816579 5832930278541458185224869)
                  ·
                    refine ⟨1093674427226523409729663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5832930278541458185224869 1093674427226523409729663)
                    ·
                      rfl

theorem cell23_6389770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 4, 1, 4].length) (baseStart_6389770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6389770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6389770 prefixEnd_6389770 := by exact prefixLift 6389770
  have htrace : WordTrace (prefixWord ++ tailWord_6389770) baseStart_6389770 baseEnd_6389770 := by
    simpa [prefixWord, tailWord_6389770, baseEnd_6389770] using wordTrace_append hprefix tailTrace_6389770
  have hstable : (prefixWord ++ tailWord_6389770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6389770).length < 2 ^ (prefixWord ++ tailWord_6389770).sum := by decide
  have hdescent : baseEnd_6389770 < baseStart_6389770 := by decide
  rcases family_descends (prefixWord ++ tailWord_6389770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6389779 : List Nat := [1, 1, 1, 2, 1, 4, 3, 2, 3, 5]
def baseStart_6389779 : Nat := 118140960795 + 6389779 * 2 ^ 59
def prefixEnd_6389779 : Nat := 4983230072969 + 3 ^ 40 * 6389779 * 2
def baseEnd_6389779 : Nat := 1093675967668486897992149

theorem tailTrace_6389779 : CollatzResearch.WordTrace tailWord_6389779 prefixEnd_6389779 1093675967668486897992149 := by
  unfold tailWord_6389779
  simp only [CollatzResearch.WordTrace]
  refine ⟨233054386317929445216484391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155369590878619630144322927 233054386317929445216484391)
  ·
    refine ⟨349581579476894167824726587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233054386317929445216484391 349581579476894167824726587)
    ·
      refine ⟨524372369215341251737089881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349581579476894167824726587 524372369215341251737089881)
      ·
        refine ⟨393279276911505938802817411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 524372369215341251737089881 393279276911505938802817411)
        ·
          refine ⟨589918915367258908204226117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 393279276911505938802817411 589918915367258908204226117)
          ·
            refine ⟨110609796631361045288292397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 589918915367258908204226117 110609796631361045288292397)
            ·
              refine ⟨41478673736760391983109649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110609796631361045288292397 41478673736760391983109649)
              ·
                refine ⟨31109005302570293987332237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41478673736760391983109649 31109005302570293987332237)
                ·
                  refine ⟨11665876988463860245249589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31109005302570293987332237 11665876988463860245249589)
                  ·
                    refine ⟨1093675967668486897992149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11665876988463860245249589 1093675967668486897992149)
                    ·
                      rfl

theorem cell23_6389779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 3, 5].length) (baseStart_6389779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6389779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6389779 prefixEnd_6389779 := by exact prefixLift 6389779
  have htrace : WordTrace (prefixWord ++ tailWord_6389779) baseStart_6389779 baseEnd_6389779 := by
    simpa [prefixWord, tailWord_6389779, baseEnd_6389779] using wordTrace_append hprefix tailTrace_6389779
  have hstable : (prefixWord ++ tailWord_6389779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6389779).length < 2 ^ (prefixWord ++ tailWord_6389779).sum := by decide
  have hdescent : baseEnd_6389779 < baseStart_6389779 := by decide
  rcases family_descends (prefixWord ++ tailWord_6389779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6389810 : List Nat := [3, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3]
def baseStart_6389810 : Nat := 118140960795 + 6389810 * 2 ^ 59
def prefixEnd_6389810 : Nat := 4983230072969 + 3 ^ 40 * 6389810 * 2
def baseEnd_6389810 : Nat := 3281043820905750072688805

theorem tailTrace_6389810 : CollatzResearch.WordTrace tailWord_6389810 prefixEnd_6389810 3281043820905750072688805 := by
  unfold tailWord_6389810
  simp only [CollatzResearch.WordTrace]
  refine ⟨58263879245204284377715721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155370344653878091673908589 58263879245204284377715721)
  ·
    refine ⟨43697909433903213283286791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58263879245204284377715721 43697909433903213283286791)
    ·
      refine ⟨65546864150854819924930187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43697909433903213283286791 65546864150854819924930187)
      ·
        refine ⟨98320296226282229887395281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65546864150854819924930187 98320296226282229887395281)
        ·
          refine ⟨73740222169711672415546461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98320296226282229887395281 73740222169711672415546461)
          ·
            refine ⟨27652583313641877155829923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73740222169711672415546461 27652583313641877155829923)
            ·
              refine ⟨41478874970462815733744885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27652583313641877155829923 41478874970462815733744885)
              ·
                refine ⟨3888644528480888975038583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41478874970462815733744885 3888644528480888975038583)
                ·
                  refine ⟨5832966792721333462557875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3888644528480888975038583 5832966792721333462557875)
                  ·
                    refine ⟨8749450189082000193836813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5832966792721333462557875 8749450189082000193836813)
                    ·
                      refine ⟨3281043820905750072688805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8749450189082000193836813 3281043820905750072688805)
                      ·
                        rfl

theorem cell23_6389810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3].length) (baseStart_6389810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6389810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6389810 prefixEnd_6389810 := by exact prefixLift 6389810
  have htrace : WordTrace (prefixWord ++ tailWord_6389810) baseStart_6389810 baseEnd_6389810 := by
    simpa [prefixWord, tailWord_6389810, baseEnd_6389810] using wordTrace_append hprefix tailTrace_6389810
  have hstable : (prefixWord ++ tailWord_6389810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6389810).length < 2 ^ (prefixWord ++ tailWord_6389810).sum := by decide
  have hdescent : baseEnd_6389810 < baseStart_6389810 := by decide
  rcases family_descends (prefixWord ++ tailWord_6389810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6389813 : List Nat := [1, 3, 3, 1, 1, 1, 6, 1, 1, 5]
def baseStart_6389813 : Nat := 118140960795 + 6389813 * 2 ^ 59
def prefixEnd_6389813 : Nat := 4983230072969 + 3 ^ 40 * 6389813 * 2
def baseEnd_6389813 : Nat := 1093681787115904520317097

theorem tailTrace_6389813 : CollatzResearch.WordTrace tailWord_6389813 prefixEnd_6389813 1093681787115904520317097 := by
  unfold tailWord_6389813
  simp only [CollatzResearch.WordTrace]
  refine ⟨233055626399806269023222093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155370417599870846015481395 233055626399806269023222093)
  ·
    refine ⟨87395859899927350883708285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233055626399806269023222093 87395859899927350883708285)
    ·
      refine ⟨32773447462472756581390607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87395859899927350883708285 32773447462472756581390607)
      ·
        refine ⟨49160171193709134872085911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32773447462472756581390607 49160171193709134872085911)
        ·
          refine ⟨73740256790563702308128867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49160171193709134872085911 73740256790563702308128867)
          ·
            refine ⟨110610385185845553462193301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73740256790563702308128867 110610385185845553462193301)
            ·
              refine ⟨5184861805586510318540311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 110610385185845553462193301 5184861805586510318540311)
              ·
                refine ⟨7777292708379765477810467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5184861805586510318540311 7777292708379765477810467)
                ·
                  refine ⟨11665939062569648216715701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7777292708379765477810467 11665939062569648216715701)
                  ·
                    refine ⟨1093681787115904520317097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11665939062569648216715701 1093681787115904520317097)
                    ·
                      rfl

theorem cell23_6389813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6, 1, 1, 5].length) (baseStart_6389813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6389813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6389813 prefixEnd_6389813 := by exact prefixLift 6389813
  have htrace : WordTrace (prefixWord ++ tailWord_6389813) baseStart_6389813 baseEnd_6389813 := by
    simpa [prefixWord, tailWord_6389813, baseEnd_6389813] using wordTrace_append hprefix tailTrace_6389813
  have hstable : (prefixWord ++ tailWord_6389813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6389813).length < 2 ^ (prefixWord ++ tailWord_6389813).sum := by decide
  have hdescent : baseEnd_6389813 < baseStart_6389813 := by decide
  rcases family_descends (prefixWord ++ tailWord_6389813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6389829 : List Nat := [1, 3, 1, 1, 1, 3, 1, 4, 1, 1, 6]
def baseStart_6389829 : Nat := 118140960795 + 6389829 * 2 ^ 59
def prefixEnd_6389829 : Nat := 4983230072969 + 3 ^ 40 * 6389829 * 2
def baseEnd_6389829 : Nat := 3281053577038185498351217

theorem tailTrace_6389829 : CollatzResearch.WordTrace tailWord_6389829 prefixEnd_6389829 3281053577038185498351217 := by
  unfold tailWord_6389829
  simp only [CollatzResearch.WordTrace]
  refine ⟨233056209967748303755804541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155370806645165535837203027 233056209967748303755804541)
  ·
    refine ⟨87396078737905613908426703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233056209967748303755804541 87396078737905613908426703)
    ·
      refine ⟨131094118106858420862640055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87396078737905613908426703 131094118106858420862640055)
      ·
        refine ⟨196641177160287631293960083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131094118106858420862640055 196641177160287631293960083)
        ·
          refine ⟨294961765740431446940940125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196641177160287631293960083 294961765740431446940940125)
          ·
            refine ⟨110610662152661792602852547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 294961765740431446940940125 110610662152661792602852547)
            ·
              refine ⟨165915993228992688904278821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110610662152661792602852547 165915993228992688904278821)
              ·
                refine ⟨31109248730436129169552279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 165915993228992688904278821 31109248730436129169552279)
                ·
                  refine ⟨46663873095654193754328419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31109248730436129169552279 46663873095654193754328419)
                  ·
                    refine ⟨69995809643481290631492629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46663873095654193754328419 69995809643481290631492629)
                    ·
                      refine ⟨3281053577038185498351217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69995809643481290631492629 3281053577038185498351217)
                      ·
                        rfl

theorem cell23_6389829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 1, 6].length) (baseStart_6389829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6389829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6389829 prefixEnd_6389829 := by exact prefixLift 6389829
  have htrace : WordTrace (prefixWord ++ tailWord_6389829) baseStart_6389829 baseEnd_6389829 := by
    simpa [prefixWord, tailWord_6389829, baseEnd_6389829] using wordTrace_append hprefix tailTrace_6389829
  have hstable : (prefixWord ++ tailWord_6389829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6389829).length < 2 ^ (prefixWord ++ tailWord_6389829).sum := by decide
  have hdescent : baseEnd_6389829 < baseStart_6389829 := by decide
  rcases family_descends (prefixWord ++ tailWord_6389829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6389836 : List Nat := [2, 2, 1, 3, 1, 1, 2, 1, 5, 2, 3]
def baseStart_6389836 : Nat := 118140960795 + 6389836 * 2 ^ 59
def prefixEnd_6389836 : Nat := 4983230072969 + 3 ^ 40 * 6389836 * 2
def baseEnd_6389836 : Nat := 3281057171402766970963685

theorem tailTrace_6389836 : CollatzResearch.WordTrace tailWord_6389836 prefixEnd_6389836 3281057171402766970963685 := by
  unfold tailWord_6389836
  simp only [CollatzResearch.WordTrace]
  refine ⟨116528232639361471975654681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155370976852481962634206241 116528232639361471975654681)
  ·
    refine ⟨87396174479521103981741011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116528232639361471975654681 87396174479521103981741011)
    ·
      refine ⟨131094261719281655972611517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87396174479521103981741011 131094261719281655972611517)
      ·
        refine ⟨49160348144730620989729319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131094261719281655972611517 49160348144730620989729319)
        ·
          refine ⟨73740522217095931484593979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49160348144730620989729319 73740522217095931484593979)
          ·
            refine ⟨110610783325643897226890969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73740522217095931484593979 110610783325643897226890969)
            ·
              refine ⟨82958087494232922920168227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110610783325643897226890969 82958087494232922920168227)
              ·
                refine ⟨124437131241349384380252341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82958087494232922920168227 124437131241349384380252341)
                ·
                  refine ⟨11665981053876504785648657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 124437131241349384380252341 11665981053876504785648657)
                  ·
                    refine ⟨8749485790407378589236493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11665981053876504785648657 8749485790407378589236493)
                    ·
                      refine ⟨3281057171402766970963685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8749485790407378589236493 3281057171402766970963685)
                      ·
                        rfl

theorem cell23_6389836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_6389836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6389836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6389836 prefixEnd_6389836 := by exact prefixLift 6389836
  have htrace : WordTrace (prefixWord ++ tailWord_6389836) baseStart_6389836 baseEnd_6389836 := by
    simpa [prefixWord, tailWord_6389836, baseEnd_6389836] using wordTrace_append hprefix tailTrace_6389836
  have hstable : (prefixWord ++ tailWord_6389836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6389836).length < 2 ^ (prefixWord ++ tailWord_6389836).sum := by decide
  have hdescent : baseEnd_6389836 < baseStart_6389836 := by decide
  rcases family_descends (prefixWord ++ tailWord_6389836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6389856 : List Nat := [2, 1, 1, 3, 2, 3, 4, 7]
def baseStart_6389856 : Nat := 118140960795 + 6389856 * 2 ^ 59
def prefixEnd_6389856 : Nat := 4983230072969 + 3 ^ 40 * 6389856 * 2
def baseEnd_6389856 : Nat := 121521016333920625656059

theorem tailTrace_6389856 : CollatzResearch.WordTrace tailWord_6389856 prefixEnd_6389856 121521016333920625656059 := by
  unfold tailWord_6389856
  simp only [CollatzResearch.WordTrace]
  refine ⟨116528597369325243683518711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155371463159100324911358281 116528597369325243683518711)
  ·
    refine ⟨174792896053987865525278067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116528597369325243683518711 174792896053987865525278067)
    ·
      refine ⟨262189344080981798287917101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174792896053987865525278067 262189344080981798287917101)
      ·
        refine ⟨98321004030368174357968913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 262189344080981798287917101 98321004030368174357968913)
        ·
          refine ⟨73740753022776130768476685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98321004030368174357968913 73740753022776130768476685)
          ·
            refine ⟨27652782383541049038178757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73740753022776130768476685 27652782383541049038178757)
            ·
              refine ⟨5184896696913946694658517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27652782383541049038178757 5184896696913946694658517)
              ·
                refine ⟨121521016333920625656059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5184896696913946694658517 121521016333920625656059)
                ·
                  rfl

theorem cell23_6389856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4, 7].length) (baseStart_6389856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6389856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6389856 prefixEnd_6389856 := by exact prefixLift 6389856
  have htrace : WordTrace (prefixWord ++ tailWord_6389856) baseStart_6389856 baseEnd_6389856 := by
    simpa [prefixWord, tailWord_6389856, baseEnd_6389856] using wordTrace_append hprefix tailTrace_6389856
  have hstable : (prefixWord ++ tailWord_6389856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6389856).length < 2 ^ (prefixWord ++ tailWord_6389856).sum := by decide
  have hdescent : baseEnd_6389856 < baseStart_6389856 := by decide
  rcases family_descends (prefixWord ++ tailWord_6389856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6389884 : List Nat := [2, 2, 2, 1, 1, 5, 3, 2, 1, 2, 2]
def baseStart_6389884 : Nat := 118140960795 + 6389884 * 2 ^ 59
def prefixEnd_6389884 : Nat := 4983230072969 + 3 ^ 40 * 6389884 * 2
def baseEnd_6389884 : Nat := 3281081818474182783163465

theorem tailTrace_6389884 : CollatzResearch.WordTrace tailWord_6389884 prefixEnd_6389884 3281081818474182783163465 := by
  unfold tailWord_6389884
  simp only [CollatzResearch.WordTrace]
  refine ⟨116529107991274524074528353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155372143988366032099371137 116529107991274524074528353)
  ·
    refine ⟨87396830993455893055896265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116529107991274524074528353 87396830993455893055896265)
    ·
      refine ⟨65547623245091919791922199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87396830993455893055896265 65547623245091919791922199)
      ·
        refine ⟨98321434867637879687883299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65547623245091919791922199 98321434867637879687883299)
        ·
          refine ⟨147482152301456819531824949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98321434867637879687883299 147482152301456819531824949)
          ·
            refine ⟨13826451778261576831108589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 147482152301456819531824949 13826451778261576831108589)
            ·
              refine ⟨5184919416848091311665721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13826451778261576831108589 5184919416848091311665721)
              ·
                refine ⟨3888689562636068483749291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5184919416848091311665721 3888689562636068483749291)
                ·
                  refine ⟨5833034343954102725623937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3888689562636068483749291 5833034343954102725623937)
                  ·
                    refine ⟨4374775757965577044217953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5833034343954102725623937 4374775757965577044217953)
                    ·
                      refine ⟨3281081818474182783163465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4374775757965577044217953 3281081818474182783163465)
                      ·
                        rfl

theorem cell23_6389884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3, 2, 1, 2, 2].length) (baseStart_6389884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6389884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6389884 prefixEnd_6389884 := by exact prefixLift 6389884
  have htrace : WordTrace (prefixWord ++ tailWord_6389884) baseStart_6389884 baseEnd_6389884 := by
    simpa [prefixWord, tailWord_6389884, baseEnd_6389884] using wordTrace_append hprefix tailTrace_6389884
  have hstable : (prefixWord ++ tailWord_6389884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6389884).length < 2 ^ (prefixWord ++ tailWord_6389884).sum := by decide
  have hdescent : baseEnd_6389884 < baseStart_6389884 := by decide
  rcases family_descends (prefixWord ++ tailWord_6389884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6390033 : List Nat := [1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 3]
def baseStart_6390033 : Nat := 118140960795 + 6390033 * 2 ^ 59
def prefixEnd_6390033 : Nat := 4983230072969 + 3 ^ 40 * 6390033 * 2
def baseEnd_6390033 : Nat := 3281158327091702700200279

theorem tailTrace_6390033 : CollatzResearch.WordTrace tailWord_6390033 prefixEnd_6390033 3281158327091702700200279 := by
  unfold tailWord_6390033
  simp only [CollatzResearch.WordTrace]
  refine ⟨233063650459009246596230753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155375766972672831064153835 233063650459009246596230753)
  ·
    refine ⟨174797737844256934947173065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233063650459009246596230753 174797737844256934947173065)
    ·
      refine ⟨131098303383192701210379799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174797737844256934947173065 131098303383192701210379799)
      ·
        refine ⟨196647455074789051815569699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131098303383192701210379799 196647455074789051815569699)
        ·
          refine ⟨294971182612183577723354549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196647455074789051815569699 294971182612183577723354549)
          ·
            refine ⟨27653548369892210411564489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 294971182612183577723354549 27653548369892210411564489)
            ·
              refine ⟨20740161277419157808673367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27653548369892210411564489 20740161277419157808673367)
              ·
                refine ⟨31110241916128736713010051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20740161277419157808673367 31110241916128736713010051)
                ·
                  refine ⟨46665362874193105069515077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31110241916128736713010051 46665362874193105069515077)
                  ·
                    refine ⟨8749755538911207200534077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46665362874193105069515077 8749755538911207200534077)
                    ·
                      refine ⟨3281158327091702700200279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8749755538911207200534077 3281158327091702700200279)
                      ·
                        rfl

theorem cell23_6390033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 3].length) (baseStart_6390033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6390033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6390033 prefixEnd_6390033 := by exact prefixLift 6390033
  have htrace : WordTrace (prefixWord ++ tailWord_6390033) baseStart_6390033 baseEnd_6390033 := by
    simpa [prefixWord, tailWord_6390033, baseEnd_6390033] using wordTrace_append hprefix tailTrace_6390033
  have hstable : (prefixWord ++ tailWord_6390033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6390033).length < 2 ^ (prefixWord ++ tailWord_6390033).sum := by decide
  have hdescent : baseEnd_6390033 < baseStart_6390033 := by decide
  rcases family_descends (prefixWord ++ tailWord_6390033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6390050 : List Nat := [3, 3, 1, 1, 3, 1, 1, 1, 4, 2, 3]
def baseStart_6390050 : Nat := 118140960795 + 6390050 * 2 ^ 59
def prefixEnd_6390050 : Nat := 4983230072969 + 3 ^ 40 * 6390050 * 2
def baseEnd_6390050 : Nat := 3281167056262829133687701

theorem tailTrace_6390050 : CollatzResearch.WordTrace tailWord_6390050 prefixEnd_6390050 3281167056262829133687701 := by
  unfold tailWord_6390050
  simp only [CollatzResearch.WordTrace]
  refine ⟨58266067624986914624899901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155376180333298438999733069 58266067624986914624899901)
  ·
    refine ⟨21849775359370092984337463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58266067624986914624899901 21849775359370092984337463)
    ·
      refine ⟨32774663039055139476506195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21849775359370092984337463 32774663039055139476506195)
      ·
        refine ⟨49161994558582709214759293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32774663039055139476506195 49161994558582709214759293)
        ·
          refine ⟨18435747959468515955534735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49161994558582709214759293 18435747959468515955534735)
          ·
            refine ⟨27653621939202773933302103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18435747959468515955534735 27653621939202773933302103)
            ·
              refine ⟨41480432908804160899953155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27653621939202773933302103 41480432908804160899953155)
              ·
                refine ⟨62220649363206241349929733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41480432908804160899953155 62220649363206241349929733)
                ·
                  refine ⟨11666371755601170253111825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62220649363206241349929733 11666371755601170253111825)
                  ·
                    refine ⟨8749778816700877689833869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11666371755601170253111825 8749778816700877689833869)
                    ·
                      refine ⟨3281167056262829133687701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8749778816700877689833869 3281167056262829133687701)
                      ·
                        rfl

theorem cell23_6390050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_6390050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6390050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6390050 prefixEnd_6390050 := by exact prefixLift 6390050
  have htrace : WordTrace (prefixWord ++ tailWord_6390050) baseStart_6390050 baseEnd_6390050 := by
    simpa [prefixWord, tailWord_6390050, baseEnd_6390050] using wordTrace_append hprefix tailTrace_6390050
  have hstable : (prefixWord ++ tailWord_6390050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6390050).length < 2 ^ (prefixWord ++ tailWord_6390050).sum := by decide
  have hdescent : baseEnd_6390050 < baseStart_6390050 := by decide
  rcases family_descends (prefixWord ++ tailWord_6390050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6390084 : List Nat := [2, 3, 4, 1, 2, 1, 2, 1, 2, 2, 3]
def baseStart_6390084 : Nat := 118140960795 + 6390084 * 2 ^ 59
def prefixEnd_6390084 : Nat := 4983230072969 + 3 ^ 40 * 6390084 * 2
def baseEnd_6390084 : Nat := 3281184514605082000662545

theorem tailTrace_6390084 : CollatzResearch.WordTrace tailWord_6390084 prefixEnd_6390084 3281184514605082000662545 := by
  unfold tailWord_6390084
  simp only [CollatzResearch.WordTrace]
  refine ⟨116532755290912241153168653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155377007054549654870891537 116532755290912241153168653)
  ·
    refine ⟨43699783234092090432438245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116532755290912241153168653 43699783234092090432438245)
    ·
      refine ⟨8193709356392266956082171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43699783234092090432438245 8193709356392266956082171)
      ·
        refine ⟨12290564034588400434123257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8193709356392266956082171 12290564034588400434123257)
        ·
          refine ⟨9217923025941300325592443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12290564034588400434123257 9217923025941300325592443)
          ·
            refine ⟨13826884538911950488388665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9217923025941300325592443 13826884538911950488388665)
            ·
              refine ⟨10370163404183962866291499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13826884538911950488388665 10370163404183962866291499)
              ·
                refine ⟨15555245106275944299437249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10370163404183962866291499 15555245106275944299437249)
                ·
                  refine ⟨11666433829706958224577937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15555245106275944299437249 11666433829706958224577937)
                  ·
                    refine ⟨8749825372280218668433453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11666433829706958224577937 8749825372280218668433453)
                    ·
                      refine ⟨3281184514605082000662545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8749825372280218668433453 3281184514605082000662545)
                      ·
                        rfl

theorem cell23_6390084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_6390084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6390084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6390084 prefixEnd_6390084 := by exact prefixLift 6390084
  have htrace : WordTrace (prefixWord ++ tailWord_6390084) baseStart_6390084 baseEnd_6390084 := by
    simpa [prefixWord, tailWord_6390084, baseEnd_6390084] using wordTrace_append hprefix tailTrace_6390084
  have hstable : (prefixWord ++ tailWord_6390084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6390084).length < 2 ^ (prefixWord ++ tailWord_6390084).sum := by decide
  have hdescent : baseEnd_6390084 < baseStart_6390084 := by decide
  rcases family_descends (prefixWord ++ tailWord_6390084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6390108 : List Nat := [2, 2, 4, 3, 1, 2, 2, 2, 1, 4]
def baseStart_6390108 : Nat := 118140960795 + 6390108 * 2 ^ 59
def prefixEnd_6390108 : Nat := 4983230072969 + 3 ^ 40 * 6390108 * 2
def baseEnd_6390108 : Nat := 1093732279380263302254145

theorem tailTrace_6390108 : CollatzResearch.WordTrace tailWord_6390108 prefixEnd_6390108 1093732279380263302254145 := by
  unfold tailWord_6390108
  simp only [CollatzResearch.WordTrace]
  refine ⟨116533192966868767202605489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155377590622491689603473985 116533192966868767202605489)
  ·
    refine ⟨87399894725151575401954117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116533192966868767202605489 87399894725151575401954117)
    ·
      refine ⟨16387480260965920387866397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87399894725151575401954117 16387480260965920387866397)
      ·
        refine ⟨6145305097862220145449899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16387480260965920387866397 6145305097862220145449899)
        ·
          refine ⟨9217957646793330218174849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6145305097862220145449899 9217957646793330218174849)
          ·
            refine ⟨6913468235094997663631137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9217957646793330218174849 6913468235094997663631137)
            ·
              refine ⟨5185101176321248247723353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6913468235094997663631137 5185101176321248247723353)
              ·
                refine ⟨3888825882240936185792515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5185101176321248247723353 3888825882240936185792515)
                ·
                  refine ⟨5833238823361404278688773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3888825882240936185792515 5833238823361404278688773)
                  ·
                    refine ⟨1093732279380263302254145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5833238823361404278688773 1093732279380263302254145)
                    ·
                      rfl

theorem cell23_6390108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_6390108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6390108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6390108 prefixEnd_6390108 := by exact prefixLift 6390108
  have htrace : WordTrace (prefixWord ++ tailWord_6390108) baseStart_6390108 baseEnd_6390108 := by
    simpa [prefixWord, tailWord_6390108, baseEnd_6390108] using wordTrace_append hprefix tailTrace_6390108
  have hstable : (prefixWord ++ tailWord_6390108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6390108).length < 2 ^ (prefixWord ++ tailWord_6390108).sum := by decide
  have hdescent : baseEnd_6390108 < baseStart_6390108 := by decide
  rcases family_descends (prefixWord ++ tailWord_6390108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6390120 : List Nat := [2, 1, 4, 2, 2, 1, 1, 2, 3, 1, 4]
def baseStart_6390120 : Nat := 118140960795 + 6390120 * 2 ^ 59
def prefixEnd_6390120 : Nat := 4983230072969 + 3 ^ 40 * 6390120 * 2
def baseEnd_6390120 : Nat := 3281202999908643859812379

theorem tailTrace_6390120 : CollatzResearch.WordTrace tailWord_6390120 prefixEnd_6390120 3281202999908643859812379 := by
  unfold tailWord_6390120
  simp only [CollatzResearch.WordTrace]
  refine ⟨116533411804847030227323907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155377882406462706969765209 116533411804847030227323907)
  ·
    refine ⟨174800117707270545340985861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116533411804847030227323907 174800117707270545340985861)
    ·
      refine ⟨32775022070113227251434849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 174800117707270545340985861 32775022070113227251434849)
      ·
        refine ⟨24581266552584920438576137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32775022070113227251434849 24581266552584920438576137)
        ·
          refine ⟨18435949914438690328932103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24581266552584920438576137 18435949914438690328932103)
          ·
            refine ⟨27653924871658035493398155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18435949914438690328932103 27653924871658035493398155)
            ·
              refine ⟨41480887307487053240097233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27653924871658035493398155 41480887307487053240097233)
              ·
                refine ⟨31110665480615289930072925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41480887307487053240097233 31110665480615289930072925)
                ·
                  refine ⟨11666499555230733723777347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31110665480615289930072925 11666499555230733723777347)
                  ·
                    refine ⟨17499749332846100585666021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11666499555230733723777347 17499749332846100585666021)
                    ·
                      refine ⟨3281202999908643859812379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17499749332846100585666021 3281202999908643859812379)
                      ·
                        rfl

theorem cell23_6390120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_6390120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6390120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6390120 prefixEnd_6390120 := by exact prefixLift 6390120
  have htrace : WordTrace (prefixWord ++ tailWord_6390120) baseStart_6390120 baseEnd_6390120 := by
    simpa [prefixWord, tailWord_6390120, baseEnd_6390120] using wordTrace_append hprefix tailTrace_6390120
  have hstable : (prefixWord ++ tailWord_6390120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6390120).length < 2 ^ (prefixWord ++ tailWord_6390120).sum := by decide
  have hdescent : baseEnd_6390120 < baseStart_6390120 := by decide
  rcases family_descends (prefixWord ++ tailWord_6390120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6390130 : List Nat := [3, 2, 1, 2, 1, 4, 2, 1, 1, 6]
def baseStart_6390130 : Nat := 118140960795 + 6390130 * 2 ^ 59
def prefixEnd_6390130 : Nat := 4983230072969 + 3 ^ 40 * 6390130 * 2
def baseEnd_6390130 : Nat := 1093736044905062940229111

theorem tailTrace_6390130 : CollatzResearch.WordTrace tailWord_6390130 prefixEnd_6390130 1093736044905062940229111 := by
  unfold tailWord_6390130
  simp only [CollatzResearch.WordTrace]
  refine ⟨58266797084914458040627961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155378125559771888108341229 58266797084914458040627961)
  ·
    refine ⟨43700097813685843530470971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58266797084914458040627961 43700097813685843530470971)
    ·
      refine ⟨65550146720528765295706457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43700097813685843530470971 65550146720528765295706457)
      ·
        refine ⟨49162610040396573971779843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65550146720528765295706457 49162610040396573971779843)
        ·
          refine ⟨73743915060594860957669765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49162610040396573971779843 73743915060594860957669765)
          ·
            refine ⟨13826984073861536429563081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73743915060594860957669765 13826984073861536429563081)
            ·
              refine ⟨10370238055396152322172311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13826984073861536429563081 10370238055396152322172311)
              ·
                refine ⟨15555357083094228483258467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10370238055396152322172311 15555357083094228483258467)
                ·
                  refine ⟨23333035624641342724887701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15555357083094228483258467 23333035624641342724887701)
                  ·
                    refine ⟨1093736044905062940229111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23333035624641342724887701 1093736044905062940229111)
                    ·
                      rfl

theorem cell23_6390130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 1, 1, 6].length) (baseStart_6390130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6390130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6390130 prefixEnd_6390130 := by exact prefixLift 6390130
  have htrace : WordTrace (prefixWord ++ tailWord_6390130) baseStart_6390130 baseEnd_6390130 := by
    simpa [prefixWord, tailWord_6390130, baseEnd_6390130] using wordTrace_append hprefix tailTrace_6390130
  have hstable : (prefixWord ++ tailWord_6390130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6390130).length < 2 ^ (prefixWord ++ tailWord_6390130).sum := by decide
  have hdescent : baseEnd_6390130 < baseStart_6390130 := by decide
  rcases family_descends (prefixWord ++ tailWord_6390130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6390154 : List Nat := [3, 1, 2, 5, 1, 1, 1, 3, 1, 1, 4]
def baseStart_6390154 : Nat := 118140960795 + 6390154 * 2 ^ 59
def prefixEnd_6390154 : Nat := 4983230072969 + 3 ^ 40 * 6390154 * 2
def baseEnd_6390154 : Nat := 3281220458250896726787223

theorem tailTrace_6390154 : CollatzResearch.WordTrace tailWord_6390154 prefixEnd_6390154 3281220458250896726787223 := by
  unfold tailWord_6390154
  simp only [CollatzResearch.WordTrace]
  refine ⟨58267015922892721065346379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155378709127713922840923677 58267015922892721065346379)
  ·
    refine ⟨87400523884339081598019569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58267015922892721065346379 87400523884339081598019569)
    ·
      refine ⟨65550392913254311198514677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87400523884339081598019569 65550392913254311198514677)
      ·
        refine ⟨6145349335617591674860751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65550392913254311198514677 6145349335617591674860751)
        ·
          refine ⟨9218024003426387512291127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6145349335617591674860751 9218024003426387512291127)
          ·
            refine ⟨13827036005139581268436691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9218024003426387512291127 13827036005139581268436691)
            ·
              refine ⟨20740554007709371902655037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13827036005139581268436691 20740554007709371902655037)
              ·
                refine ⟨7777707752891014463495639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20740554007709371902655037 7777707752891014463495639)
                ·
                  refine ⟨11666561629336521695243459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7777707752891014463495639 11666561629336521695243459)
                  ·
                    refine ⟨17499842444004782542865189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11666561629336521695243459 17499842444004782542865189)
                    ·
                      refine ⟨3281220458250896726787223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17499842444004782542865189 3281220458250896726787223)
                      ·
                        rfl

theorem cell23_6390154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_6390154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6390154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6390154 prefixEnd_6390154 := by exact prefixLift 6390154
  have htrace : WordTrace (prefixWord ++ tailWord_6390154) baseStart_6390154 baseEnd_6390154 := by
    simpa [prefixWord, tailWord_6390154, baseEnd_6390154] using wordTrace_append hprefix tailTrace_6390154
  have hstable : (prefixWord ++ tailWord_6390154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6390154).length < 2 ^ (prefixWord ++ tailWord_6390154).sum := by decide
  have hdescent : baseEnd_6390154 < baseStart_6390154 := by decide
  rcases family_descends (prefixWord ++ tailWord_6390154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6390184 : List Nat := [2, 1, 6, 1, 1, 3, 1, 1, 1, 2, 4]
def baseStart_6390184 : Nat := 118140960795 + 6390184 * 2 ^ 59
def prefixEnd_6390184 : Nat := 4983230072969 + 3 ^ 40 * 6390184 * 2
def baseEnd_6390184 : Nat := 3281235862670531609412085

theorem tailTrace_6390184 : CollatzResearch.WordTrace tailWord_6390184 prefixEnd_6390184 3281235862670531609412085 := by
  unfold tailWord_6390184
  simp only [CollatzResearch.WordTrace]
  refine ⟨116534578940731099692488803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155379438587641466256651737 116534578940731099692488803)
  ·
    refine ⟨174801868411096649538733205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116534578940731099692488803 174801868411096649538733205)
    ·
      refine ⟨8193837581770155447128119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 174801868411096649538733205 8193837581770155447128119)
      ·
        refine ⟨12290756372655233170692179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8193837581770155447128119 12290756372655233170692179)
        ·
          refine ⟨18436134558982849756038269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12290756372655233170692179 18436134558982849756038269)
          ·
            refine ⟨6913550459618568658514351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18436134558982849756038269 6913550459618568658514351)
            ·
              refine ⟨10370325689427852987771527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6913550459618568658514351 10370325689427852987771527)
              ·
                refine ⟨15555488534141779481657291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10370325689427852987771527 15555488534141779481657291)
                ·
                  refine ⟨23333232801212669222485937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15555488534141779481657291 23333232801212669222485937)
                  ·
                    refine ⟨17499924600909501916864453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23333232801212669222485937 17499924600909501916864453)
                    ·
                      refine ⟨3281235862670531609412085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17499924600909501916864453 3281235862670531609412085)
                      ·
                        rfl

theorem cell23_6390184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_6390184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6390184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6390184 prefixEnd_6390184 := by exact prefixLift 6390184
  have htrace : WordTrace (prefixWord ++ tailWord_6390184) baseStart_6390184 baseEnd_6390184 := by
    simpa [prefixWord, tailWord_6390184, baseEnd_6390184] using wordTrace_append hprefix tailTrace_6390184
  have hstable : (prefixWord ++ tailWord_6390184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6390184).length < 2 ^ (prefixWord ++ tailWord_6390184).sum := by decide
  have hdescent : baseEnd_6390184 < baseStart_6390184 := by decide
  rcases family_descends (prefixWord ++ tailWord_6390184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6390261 : List Nat := [1, 3, 5, 1, 2, 1, 1, 2, 1, 4, 2]
def baseStart_6390261 : Nat := 118140960795 + 6390261 * 2 ^ 59
def prefixEnd_6390261 : Nat := 4983230072969 + 3 ^ 40 * 6390261 * 2
def baseEnd_6390261 : Nat := 3281275400680927808149231

theorem tailTrace_6390261 : CollatzResearch.WordTrace tailWord_6390261 prefixEnd_6390261 3281275400680927808149231 := by
  unfold tailWord_6390261
  simp only [CollatzResearch.WordTrace]
  refine ⟨233071966302183241535530637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155381310868122161023687091 233071966302183241535530637)
  ·
    refine ⟨87401987363318715575823989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233071966302183241535530637 87401987363318715575823989)
    ·
      refine ⟨8193936315311129585233499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87401987363318715575823989 8193936315311129585233499)
      ·
        refine ⟨12290904472966694377850249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8193936315311129585233499 12290904472966694377850249)
        ·
          refine ⟨9218178354725020783387687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12290904472966694377850249 9218178354725020783387687)
          ·
            refine ⟨13827267532087531175081531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9218178354725020783387687 13827267532087531175081531)
            ·
              refine ⟨20740901298131296762622297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13827267532087531175081531 20740901298131296762622297)
              ·
                refine ⟨15555675973598472571966723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20740901298131296762622297 15555675973598472571966723)
                ·
                  refine ⟨23333513960397708857950085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15555675973598472571966723 23333513960397708857950085)
                  ·
                    refine ⟨4375033867574570410865641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23333513960397708857950085 4375033867574570410865641)
                    ·
                      refine ⟨3281275400680927808149231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4375033867574570410865641 3281275400680927808149231)
                      ·
                        rfl

theorem cell23_6390261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_6390261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6390261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6390261 prefixEnd_6390261 := by exact prefixLift 6390261
  have htrace : WordTrace (prefixWord ++ tailWord_6390261) baseStart_6390261 baseEnd_6390261 := by
    simpa [prefixWord, tailWord_6390261, baseEnd_6390261] using wordTrace_append hprefix tailTrace_6390261
  have hstable : (prefixWord ++ tailWord_6390261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6390261).length < 2 ^ (prefixWord ++ tailWord_6390261).sum := by decide
  have hdescent : baseEnd_6390261 < baseStart_6390261 := by decide
  rcases family_descends (prefixWord ++ tailWord_6390261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6390263 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 5, 7]
def baseStart_6390263 : Nat := 118140960795 + 6390263 * 2 ^ 59
def prefixEnd_6390263 : Nat := 4983230072969 + 3 ^ 40 * 6390263 * 2
def baseEnd_6390263 : Nat := 1093758809214078933441407

theorem tailTrace_6390263 : CollatzResearch.WordTrace tailWord_6390263 prefixEnd_6390263 1093758809214078933441407 := by
  unfold tailWord_6390263
  simp only [CollatzResearch.WordTrace]
  refine ⟨233072039248175995877103443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155381359498783997251402295 233072039248175995877103443)
  ·
    refine ⟨349608058872263993815655165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233072039248175995877103443 349608058872263993815655165)
    ·
      refine ⟨131103022077098997680870687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 349608058872263993815655165 131103022077098997680870687)
      ·
        refine ⟨196654533115648496521306031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131103022077098997680870687 196654533115648496521306031)
        ·
          refine ⟨294981799673472744781959047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196654533115648496521306031 294981799673472744781959047)
          ·
            refine ⟨442472699510209117172938571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294981799673472744781959047 442472699510209117172938571)
            ·
              refine ⟨663709049265313675759407857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 442472699510209117172938571 663709049265313675759407857)
              ·
                refine ⟨497781786948985256819555893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 663709049265313675759407857 497781786948985256819555893)
                ·
                  refine ⟨46667042526467367826833365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 497781786948985256819555893 46667042526467367826833365)
                  ·
                    refine ⟨1093758809214078933441407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46667042526467367826833365 1093758809214078933441407)
                    ·
                      rfl

theorem cell23_6390263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 7].length) (baseStart_6390263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6390263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6390263 prefixEnd_6390263 := by exact prefixLift 6390263
  have htrace : WordTrace (prefixWord ++ tailWord_6390263) baseStart_6390263 baseEnd_6390263 := by
    simpa [prefixWord, tailWord_6390263, baseEnd_6390263] using wordTrace_append hprefix tailTrace_6390263
  have hstable : (prefixWord ++ tailWord_6390263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6390263).length < 2 ^ (prefixWord ++ tailWord_6390263).sum := by decide
  have hdescent : baseEnd_6390263 < baseStart_6390263 := by decide
  rcases family_descends (prefixWord ++ tailWord_6390263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6390284 : List Nat := [2, 2, 1, 2, 4, 1, 4, 2, 5]
def baseStart_6390284 : Nat := 118140960795 + 6390284 * 2 ^ 59
def prefixEnd_6390284 : Nat := 4983230072969 + 3 ^ 40 * 6390284 * 2
def baseEnd_6390284 : Nat := 364587467859553468684625

theorem tailTrace_6390284 : CollatzResearch.WordTrace tailWord_6390284 prefixEnd_6390284 364587467859553468684625 := by
  unfold tailWord_6390284
  simp only [CollatzResearch.WordTrace]
  refine ⟨116536402590549958231808953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155381870120733277642411937 116536402590549958231808953)
  ·
    refine ⟨87402301942912468673856715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116536402590549958231808953 87402301942912468673856715)
    ·
      refine ⟨131103452914368703010785073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87402301942912468673856715 131103452914368703010785073)
      ·
        refine ⟨98327589685776527258088805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131103452914368703010785073 98327589685776527258088805)
        ·
          refine ⟨18436423066083098860891651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98327589685776527258088805 18436423066083098860891651)
          ·
            refine ⟨27654634599124648291337477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18436423066083098860891651 27654634599124648291337477)
            ·
              refine ⟨5185243987335871554625777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27654634599124648291337477 5185243987335871554625777)
              ·
                refine ⟨3888932990501903665969333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5185243987335871554625777 3888932990501903665969333)
                ·
                  refine ⟨364587467859553468684625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3888932990501903665969333 364587467859553468684625)
                  ·
                    rfl

theorem cell23_6390284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4, 2, 5].length) (baseStart_6390284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6390284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6390284 prefixEnd_6390284 := by exact prefixLift 6390284
  have htrace : WordTrace (prefixWord ++ tailWord_6390284) baseStart_6390284 baseEnd_6390284 := by
    simpa [prefixWord, tailWord_6390284, baseEnd_6390284] using wordTrace_append hprefix tailTrace_6390284
  have hstable : (prefixWord ++ tailWord_6390284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6390284).length < 2 ^ (prefixWord ++ tailWord_6390284).sum := by decide
  have hdescent : baseEnd_6390284 < baseStart_6390284 := by decide
  rcases family_descends (prefixWord ++ tailWord_6390284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6390314 : List Nat := [3, 1, 4, 1, 1, 4, 1, 1, 2, 5]
def baseStart_6390314 : Nat := 118140960795 + 6390314 * 2 ^ 59
def prefixEnd_6390314 : Nat := 4983230072969 + 3 ^ 40 * 6390314 * 2
def baseEnd_6390314 : Nat := 1093767538385205366928829

theorem tailTrace_6390314 : CollatzResearch.WordTrace tailWord_6390314 prefixEnd_6390314 1093767538385205366928829 := by
  unfold tailWord_6390314
  simp only [CollatzResearch.WordTrace]
  refine ⟨58268474842747807896802499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155382599580660821058139997 58268474842747807896802499)
  ·
    refine ⟨87402712264121711845203749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58268474842747807896802499 87402712264121711845203749)
    ·
      refine ⟨16388008549522820970975703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87402712264121711845203749 16388008549522820970975703)
      ·
        refine ⟨24582012824284231456463555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16388008549522820970975703 24582012824284231456463555)
        ·
          refine ⟨36873019236426347184695333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24582012824284231456463555 36873019236426347184695333)
          ·
            refine ⟨6913691106829940097130375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36873019236426347184695333 6913691106829940097130375)
            ·
              refine ⟨10370536660244910145695563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6913691106829940097130375 10370536660244910145695563)
              ·
                refine ⟨15555804990367365218543345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10370536660244910145695563 15555804990367365218543345)
                ·
                  refine ⟨11666853742775523913907509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15555804990367365218543345 11666853742775523913907509)
                  ·
                    refine ⟨1093767538385205366928829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11666853742775523913907509 1093767538385205366928829)
                    ·
                      rfl

theorem cell23_6390314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_6390314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6390314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6390314 prefixEnd_6390314 := by exact prefixLift 6390314
  have htrace : WordTrace (prefixWord ++ tailWord_6390314) baseStart_6390314 baseEnd_6390314 := by
    simpa [prefixWord, tailWord_6390314, baseEnd_6390314] using wordTrace_append hprefix tailTrace_6390314
  have hstable : (prefixWord ++ tailWord_6390314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6390314).length < 2 ^ (prefixWord ++ tailWord_6390314).sum := by decide
  have hdescent : baseEnd_6390314 < baseStart_6390314 := by decide
  rcases family_descends (prefixWord ++ tailWord_6390314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6390330 : List Nat := [3, 1, 1, 1, 3, 3, 1, 1, 2, 1, 6]
def baseStart_6390330 : Nat := 118140960795 + 6390330 * 2 ^ 59
def prefixEnd_6390330 : Nat := 4983230072969 + 3 ^ 40 * 6390330 * 2
def baseEnd_6390330 : Nat := 3281310830846088038186413

theorem tailTrace_6390330 : CollatzResearch.WordTrace tailWord_6390330 prefixEnd_6390330 3281310830846088038186413 := by
  unfold tailWord_6390330
  simp only [CollatzResearch.WordTrace]
  refine ⟨58268620734733316579948111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155382988625955510879861629 58268620734733316579948111)
  ·
    refine ⟨87402931102099974869922167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58268620734733316579948111 87402931102099974869922167)
    ·
      refine ⟨131104396653149962304883251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87402931102099974869922167 131104396653149962304883251)
      ·
        refine ⟨196656594979724943457324877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131104396653149962304883251 196656594979724943457324877)
        ·
          refine ⟨73746223117396853796496829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196656594979724943457324877 73746223117396853796496829)
          ·
            refine ⟨27654833669023820173686311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73746223117396853796496829 27654833669023820173686311)
            ·
              refine ⟨41482250503535730260529467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27654833669023820173686311 41482250503535730260529467)
              ·
                refine ⟨62223375755303595390794201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41482250503535730260529467 62223375755303595390794201)
                ·
                  refine ⟨46667531816477696543095651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62223375755303595390794201 46667531816477696543095651)
                  ·
                    refine ⟨70001297724716544814643477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46667531816477696543095651 70001297724716544814643477)
                    ·
                      refine ⟨3281310830846088038186413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70001297724716544814643477 3281310830846088038186413)
                      ·
                        rfl

theorem cell23_6390330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 2, 1, 6].length) (baseStart_6390330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6390330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6390330 prefixEnd_6390330 := by exact prefixLift 6390330
  have htrace : WordTrace (prefixWord ++ tailWord_6390330) baseStart_6390330 baseEnd_6390330 := by
    simpa [prefixWord, tailWord_6390330, baseEnd_6390330] using wordTrace_append hprefix tailTrace_6390330
  have hstable : (prefixWord ++ tailWord_6390330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6390330).length < 2 ^ (prefixWord ++ tailWord_6390330).sum := by decide
  have hdescent : baseEnd_6390330 < baseStart_6390330 := by decide
  rcases family_descends (prefixWord ++ tailWord_6390330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6390407 : List Nat := [1, 1, 4, 2, 1, 2, 2, 2, 3, 1, 4]
def baseStart_6390407 : Nat := 118140960795 + 6390407 * 2 ^ 59
def prefixEnd_6390407 : Nat := 4983230072969 + 3 ^ 40 * 6390407 * 2
def baseEnd_6390407 : Nat := 3281350368856484236923559

theorem tailTrace_6390407 : CollatzResearch.WordTrace tailWord_6390407 prefixEnd_6390407 3281350368856484236923559 := by
  unfold tailWord_6390407
  simp only [CollatzResearch.WordTrace]
  refine ⟨233077291359654308470345475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155384860906436205646896983 233077291359654308470345475)
  ·
    refine ⟨349615937039481462705518213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233077291359654308470345475 349615937039481462705518213)
    ·
      refine ⟨65552988194902774257284665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 349615937039481462705518213 65552988194902774257284665)
      ·
        refine ⟨49164741146177080692963499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65552988194902774257284665 49164741146177080692963499)
        ·
          refine ⟨73747111719265621039445249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49164741146177080692963499 73747111719265621039445249)
          ·
            refine ⟨55310333789449215779583937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73747111719265621039445249 55310333789449215779583937)
            ·
              refine ⟨41482750342086911834687953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55310333789449215779583937 41482750342086911834687953)
              ·
                refine ⟨31112062756565183876015965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41482750342086911834687953 31112062756565183876015965)
                ·
                  refine ⟨11667023533711943953505987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31112062756565183876015965 11667023533711943953505987)
                  ·
                    refine ⟨17500535300567915930258981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11667023533711943953505987 17500535300567915930258981)
                    ·
                      refine ⟨3281350368856484236923559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17500535300567915930258981 3281350368856484236923559)
                      ·
                        rfl

theorem cell23_6390407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_6390407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6390407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6390407 prefixEnd_6390407 := by exact prefixLift 6390407
  have htrace : WordTrace (prefixWord ++ tailWord_6390407) baseStart_6390407 baseEnd_6390407 := by
    simpa [prefixWord, tailWord_6390407, baseEnd_6390407] using wordTrace_append hprefix tailTrace_6390407
  have hstable : (prefixWord ++ tailWord_6390407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6390407).length < 2 ^ (prefixWord ++ tailWord_6390407).sum := by decide
  have hdescent : baseEnd_6390407 < baseStart_6390407 := by decide
  rcases family_descends (prefixWord ++ tailWord_6390407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6390457 : List Nat := [1, 2, 1, 4, 1, 1, 1, 1, 5, 3, 3]
def baseStart_6390457 : Nat := 118140960795 + 6390457 * 2 ^ 59
def prefixEnd_6390457 : Nat := 4983230072969 + 3 ^ 40 * 6390457 * 2
def baseEnd_6390457 : Nat := 3281376042889209041298329

theorem tailTrace_6390457 : CollatzResearch.WordTrace tailWord_6390457 prefixEnd_6390457 3281376042889209041298329 := by
  unfold tailWord_6390457
  simp only [CollatzResearch.WordTrace]
  refine ⟨233079115009473167009665625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155386076672982111339777083 233079115009473167009665625)
  ·
    refine ⟨174809336257104875257249219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233079115009473167009665625 174809336257104875257249219)
    ·
      refine ⟨262214004385657312885873829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174809336257104875257249219 262214004385657312885873829)
      ·
        refine ⟨49165125822310746166101343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 262214004385657312885873829 49165125822310746166101343)
        ·
          refine ⟨73747688733466119249152015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49165125822310746166101343 73747688733466119249152015)
          ·
            refine ⟨110621533100199178873728023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73747688733466119249152015 110621533100199178873728023)
            ·
              refine ⟨165932299650298768310592035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110621533100199178873728023 165932299650298768310592035)
              ·
                refine ⟨248898449475448152465888053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165932299650298768310592035 248898449475448152465888053)
                ·
                  refine ⟨23334229638323264293677005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 248898449475448152465888053 23334229638323264293677005)
                  ·
                    refine ⟨8750336114371224110128877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23334229638323264293677005 8750336114371224110128877)
                    ·
                      refine ⟨3281376042889209041298329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8750336114371224110128877 3281376042889209041298329)
                      ·
                        rfl

theorem cell23_6390457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_6390457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6390457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6390457 prefixEnd_6390457 := by exact prefixLift 6390457
  have htrace : WordTrace (prefixWord ++ tailWord_6390457) baseStart_6390457 baseEnd_6390457 := by
    simpa [prefixWord, tailWord_6390457, baseEnd_6390457] using wordTrace_append hprefix tailTrace_6390457
  have hstable : (prefixWord ++ tailWord_6390457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6390457).length < 2 ^ (prefixWord ++ tailWord_6390457).sum := by decide
  have hdescent : baseEnd_6390457 < baseStart_6390457 := by decide
  rcases family_descends (prefixWord ++ tailWord_6390457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6390458 : List Nat := [3, 1, 1, 1, 2, 3, 3, 4, 1, 2, 2]
def baseStart_6390458 : Nat := 118140960795 + 6390458 * 2 ^ 59
def prefixEnd_6390458 : Nat := 4983230072969 + 3 ^ 40 * 6390458 * 2
def baseEnd_6390458 : Nat := 3281376556369863537385825

theorem tailTrace_6390458 : CollatzResearch.WordTrace tailWord_6390458 prefixEnd_6390458 3281376556369863537385825 := by
  unfold tailWord_6390458
  simp only [CollatzResearch.WordTrace]
  refine ⟨58269787870617386045113007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155386100988313029453634685 58269787870617386045113007)
  ·
    refine ⟨87404681805926079067669511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58269787870617386045113007 87404681805926079067669511)
    ·
      refine ⟨131107022708889118601504267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87404681805926079067669511 131107022708889118601504267)
      ·
        refine ⟨196660534063333677902256401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131107022708889118601504267 196660534063333677902256401)
        ·
          refine ⟨147495400547500258426692301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196660534063333677902256401 147495400547500258426692301)
          ·
            refine ⟨55310775205312596910009613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147495400547500258426692301 55310775205312596910009613)
            ·
              refine ⟨20741540701992223841253605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55310775205312596910009613 20741540701992223841253605)
              ·
                refine ⟨3889038881623541970235051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20741540701992223841253605 3889038881623541970235051)
                ·
                  refine ⟨5833558322435312955352577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3889038881623541970235051 5833558322435312955352577)
                  ·
                    refine ⟨4375168741826484716514433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5833558322435312955352577 4375168741826484716514433)
                    ·
                      refine ⟨3281376556369863537385825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4375168741826484716514433 3281376556369863537385825)
                      ·
                        rfl

theorem cell23_6390458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 4, 1, 2, 2].length) (baseStart_6390458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6390458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6390458 prefixEnd_6390458 := by exact prefixLift 6390458
  have htrace : WordTrace (prefixWord ++ tailWord_6390458) baseStart_6390458 baseEnd_6390458 := by
    simpa [prefixWord, tailWord_6390458, baseEnd_6390458] using wordTrace_append hprefix tailTrace_6390458
  have hstable : (prefixWord ++ tailWord_6390458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6390458).length < 2 ^ (prefixWord ++ tailWord_6390458).sum := by decide
  have hdescent : baseEnd_6390458 < baseStart_6390458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6390458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6390474 : List Nat := [3, 1, 2, 1, 4, 1, 1, 3, 1, 3, 3]
def baseStart_6390474 : Nat := 118140960795 + 6390474 * 2 ^ 59
def prefixEnd_6390474 : Nat := 4983230072969 + 3 ^ 40 * 6390474 * 2
def baseEnd_6390474 : Nat := 3281384772060335474785751

theorem tailTrace_6390474 : CollatzResearch.WordTrace tailWord_6390474 prefixEnd_6390474 3281384772060335474785751 := by
  unfold tailWord_6390474
  simp only [CollatzResearch.WordTrace]
  refine ⟨58269933762602894728258619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155386490033607719275356317 58269933762602894728258619)
  ·
    refine ⟨87404900643904342092387929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58269933762602894728258619 87404900643904342092387929)
    ·
      refine ⟨65553675482928256569290947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87404900643904342092387929 65553675482928256569290947)
      ·
        refine ⟨98330513224392384853936421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65553675482928256569290947 98330513224392384853936421)
        ·
          refine ⟨18436971229573572160113079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98330513224392384853936421 18436971229573572160113079)
          ·
            refine ⟨27655456844360358240169619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18436971229573572160113079 27655456844360358240169619)
            ·
              refine ⟨41483185266540537360254429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27655456844360358240169619 41483185266540537360254429)
              ·
                refine ⟨15556194474952701510095411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41483185266540537360254429 15556194474952701510095411)
                ·
                  refine ⟨23334291712429052265143117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15556194474952701510095411 23334291712429052265143117)
                  ·
                    refine ⟨8750359392160894599428669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23334291712429052265143117 8750359392160894599428669)
                    ·
                      refine ⟨3281384772060335474785751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8750359392160894599428669 3281384772060335474785751)
                      ·
                        rfl

theorem cell23_6390474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 3, 1, 3, 3].length) (baseStart_6390474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6390474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6390474 prefixEnd_6390474 := by exact prefixLift 6390474
  have htrace : WordTrace (prefixWord ++ tailWord_6390474) baseStart_6390474 baseEnd_6390474 := by
    simpa [prefixWord, tailWord_6390474, baseEnd_6390474] using wordTrace_append hprefix tailTrace_6390474
  have hstable : (prefixWord ++ tailWord_6390474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6390474).length < 2 ^ (prefixWord ++ tailWord_6390474).sum := by decide
  have hdescent : baseEnd_6390474 < baseStart_6390474 := by decide
  rcases family_descends (prefixWord ++ tailWord_6390474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6390492 : List Nat := [2, 2, 5, 1, 1, 2, 2, 3, 1, 2, 2]
def baseStart_6390492 : Nat := 118140960795 + 6390492 * 2 ^ 59
def prefixEnd_6390492 : Nat := 4983230072969 + 3 ^ 40 * 6390492 * 2
def baseEnd_6390492 : Nat := 3281394014712116404360669

theorem tailTrace_6390492 : CollatzResearch.WordTrace tailWord_6390492 prefixEnd_6390492 3281394014712116404360669 := by
  unfold tailWord_6390492
  simp only [CollatzResearch.WordTrace]
  refine ⟨116540195782173183993594865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155386927709564245324793153 116540195782173183993594865)
  ·
    refine ⟨87405146836629887995196149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116540195782173183993594865 87405146836629887995196149)
    ·
      refine ⟨8194232515934051999549639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87405146836629887995196149 8194232515934051999549639)
      ·
        refine ⟨12291348773901077999324459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8194232515934051999549639 12291348773901077999324459)
        ·
          refine ⟨18437023160851616998986689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12291348773901077999324459 18437023160851616998986689)
          ·
            refine ⟨13827767370638712749240017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18437023160851616998986689 13827767370638712749240017)
            ·
              refine ⟨10370825527979034561930013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13827767370638712749240017 10370825527979034561930013)
              ·
                refine ⟨3889059572992137960723755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10370825527979034561930013 3889059572992137960723755)
                ·
                  refine ⟨5833589359488206941085633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3889059572992137960723755 5833589359488206941085633)
                  ·
                    refine ⟨4375192019616155205814225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5833589359488206941085633 4375192019616155205814225)
                    ·
                      refine ⟨3281394014712116404360669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4375192019616155205814225 3281394014712116404360669)
                      ·
                        rfl

theorem cell23_6390492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_6390492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6390492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6390492 prefixEnd_6390492 := by exact prefixLift 6390492
  have htrace : WordTrace (prefixWord ++ tailWord_6390492) baseStart_6390492 baseEnd_6390492 := by
    simpa [prefixWord, tailWord_6390492, baseEnd_6390492] using wordTrace_append hprefix tailTrace_6390492
  have hstable : (prefixWord ++ tailWord_6390492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6390492).length < 2 ^ (prefixWord ++ tailWord_6390492).sum := by decide
  have hdescent : baseEnd_6390492 < baseStart_6390492 := by decide
  rcases family_descends (prefixWord ++ tailWord_6390492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6390537 : List Nat := [1, 2, 1, 1, 3, 2, 4, 2, 7]
def baseStart_6390537 : Nat := 118140960795 + 6390537 * 2 ^ 59
def prefixEnd_6390537 : Nat := 4983230072969 + 3 ^ 40 * 6390537 * 2
def baseEnd_6390537 : Nat := 364601902371285414255329

theorem tailTrace_6390537 : CollatzResearch.WordTrace tailWord_6390537 prefixEnd_6390537 364601902371285414255329 := by
  unfold tailWord_6390537
  simp only [CollatzResearch.WordTrace]
  refine ⟨233082032849183340672577865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155388021899455560448385243 233082032849183340672577865)
  ·
    refine ⟨174811524636887505504433399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233082032849183340672577865 174811524636887505504433399)
    ·
      refine ⟨262217286955331258256650099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174811524636887505504433399 262217286955331258256650099)
      ·
        refine ⟨393325930432996887384975149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262217286955331258256650099 393325930432996887384975149)
        ·
          refine ⟨147497223912373832769365681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 393325930432996887384975149 147497223912373832769365681)
          ·
            refine ⟨110622917934280374577024261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147497223912373832769365681 110622917934280374577024261)
            ·
              refine ⟨20741797112677570233192049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110622917934280374577024261 20741797112677570233192049)
              ·
                refine ⟨15556347834508177674894037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20741797112677570233192049 15556347834508177674894037)
                ·
                  refine ⟨364601902371285414255329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15556347834508177674894037 364601902371285414255329)
                  ·
                    rfl

theorem cell23_6390537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 2, 7].length) (baseStart_6390537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6390537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6390537 prefixEnd_6390537 := by exact prefixLift 6390537
  have htrace : WordTrace (prefixWord ++ tailWord_6390537) baseStart_6390537 baseEnd_6390537 := by
    simpa [prefixWord, tailWord_6390537, baseEnd_6390537] using wordTrace_append hprefix tailTrace_6390537
  have hstable : (prefixWord ++ tailWord_6390537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6390537).length < 2 ^ (prefixWord ++ tailWord_6390537).sum := by decide
  have hdescent : baseEnd_6390537 < baseStart_6390537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6390537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6390582 : List Nat := [5, 1, 2, 2, 2, 1, 1, 3, 2, 2, 2]
def baseStart_6390582 : Nat := 118140960795 + 6390582 * 2 ^ 59
def prefixEnd_6390582 : Nat := 4983230072969 + 3 ^ 40 * 6390582 * 2
def baseEnd_6390582 : Nat := 3281440227971021052235255

theorem tailTrace_6390582 : CollatzResearch.WordTrace tailWord_6390582 prefixEnd_6390582 3281440227971021052235255 := by
  unfold tailWord_6390582
  simp only [CollatzResearch.WordTrace]
  refine ⟨14567729633376269584872875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 155389116089346875571977333 14567729633376269584872875)
  ·
    refine ⟨21851594450064404377309313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14567729633376269584872875 21851594450064404377309313)
    ·
      refine ⟨16388695837548303282981985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21851594450064404377309313 16388695837548303282981985)
      ·
        refine ⟨12291521878161227462236489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16388695837548303282981985 12291521878161227462236489)
        ·
          refine ⟨9218641408620920596677367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12291521878161227462236489 9218641408620920596677367)
          ·
            refine ⟨13827962112931380895016051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9218641408620920596677367 13827962112931380895016051)
            ·
              refine ⟨20741943169397071342524077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13827962112931380895016051 20741943169397071342524077)
              ·
                refine ⟨7778228688523901753446529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20741943169397071342524077 7778228688523901753446529)
                ·
                  refine ⟨5833671516392926315084897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7778228688523901753446529 5833671516392926315084897)
                  ·
                    refine ⟨4375253637294694736313673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5833671516392926315084897 4375253637294694736313673)
                    ·
                      refine ⟨3281440227971021052235255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4375253637294694736313673 3281440227971021052235255)
                      ·
                        rfl

theorem cell23_6390582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_6390582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6390582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6390582 prefixEnd_6390582 := by exact prefixLift 6390582
  have htrace : WordTrace (prefixWord ++ tailWord_6390582) baseStart_6390582 baseEnd_6390582 := by
    simpa [prefixWord, tailWord_6390582, baseEnd_6390582] using wordTrace_append hprefix tailTrace_6390582
  have hstable : (prefixWord ++ tailWord_6390582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6390582).length < 2 ^ (prefixWord ++ tailWord_6390582).sum := by decide
  have hdescent : baseEnd_6390582 < baseStart_6390582 := by decide
  rcases family_descends (prefixWord ++ tailWord_6390582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6390681 : List Nat := [1, 2, 1, 2, 1, 3, 1, 3, 4, 3, 2]
def baseStart_6390681 : Nat := 118140960795 + 6390681 * 2 ^ 59
def prefixEnd_6390681 : Nat := 4983230072969 + 3 ^ 40 * 6390681 * 2
def baseEnd_6390681 : Nat := 3281491062555816164897299

theorem tailTrace_6390681 : CollatzResearch.WordTrace tailWord_6390681 prefixEnd_6390681 3281491062555816164897299 := by
  unfold tailWord_6390681
  simp only [CollatzResearch.WordTrace]
  refine ⟨233087284960661653265819897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155391523307107768843879931 233087284960661653265819897)
  ·
    refine ⟨174815463720496239949364923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233087284960661653265819897 174815463720496239949364923)
    ·
      refine ⟨262223195580744359924047385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174815463720496239949364923 262223195580744359924047385)
      ·
        refine ⟨196667396685558269943035539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262223195580744359924047385 196667396685558269943035539)
        ·
          refine ⟨295001095028337404914553309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196667396685558269943035539 295001095028337404914553309)
          ·
            refine ⟨110625410635626526842957491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 295001095028337404914553309 110625410635626526842957491)
            ·
              refine ⟨165938115953439790264436237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110625410635626526842957491 165938115953439790264436237)
              ·
                refine ⟨62226793482539921349163589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 165938115953439790264436237 62226793482539921349163589)
                ·
                  refine ⟨11667523777976235252968173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62226793482539921349163589 11667523777976235252968173)
                  ·
                    refine ⟨4375321416741088219863065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11667523777976235252968173 4375321416741088219863065)
                    ·
                      refine ⟨3281491062555816164897299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4375321416741088219863065 3281491062555816164897299)
                      ·
                        rfl

theorem cell23_6390681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 4, 3, 2].length) (baseStart_6390681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6390681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6390681 prefixEnd_6390681 := by exact prefixLift 6390681
  have htrace : WordTrace (prefixWord ++ tailWord_6390681) baseStart_6390681 baseEnd_6390681 := by
    simpa [prefixWord, tailWord_6390681, baseEnd_6390681] using wordTrace_append hprefix tailTrace_6390681
  have hstable : (prefixWord ++ tailWord_6390681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6390681).length < 2 ^ (prefixWord ++ tailWord_6390681).sum := by decide
  have hdescent : baseEnd_6390681 < baseStart_6390681 := by decide
  rcases family_descends (prefixWord ++ tailWord_6390681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6390711 : List Nat := [1, 1, 3, 1, 3, 1, 3, 4, 1, 1, 4]
def baseStart_6390711 : Nat := 118140960795 + 6390711 * 2 ^ 59
def prefixEnd_6390711 : Nat := 4983230072969 + 3 ^ 40 * 6390711 * 2
def baseEnd_6390711 : Nat := 3281506466975451047522161

theorem tailTrace_6390711 : CollatzResearch.WordTrace tailWord_6390711 prefixEnd_6390711 3281506466975451047522161 := by
  unfold tailWord_6390711
  simp only [CollatzResearch.WordTrace]
  refine ⟨233088379150552968389411987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155392252767035312259607991 233088379150552968389411987)
  ·
    refine ⟨349632568725829452584117981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233088379150552968389411987 349632568725829452584117981)
    ·
      refine ⟨131112213272186044719044243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 349632568725829452584117981 131112213272186044719044243)
      ·
        refine ⟨196668319908279067078566365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131112213272186044719044243 196668319908279067078566365)
        ·
          refine ⟨73750619965604650154462387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196668319908279067078566365 73750619965604650154462387)
          ·
            refine ⟨110625929948406975231693581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73750619965604650154462387 110625929948406975231693581)
            ·
              refine ⟨41484723730652615711885093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110625929948406975231693581 41484723730652615711885093)
              ·
                refine ⟨7778385699497365445978455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41484723730652615711885093 7778385699497365445978455)
                ·
                  refine ⟨11667578549246048168967683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7778385699497365445978455 11667578549246048168967683)
                  ·
                    refine ⟨17501367823869072253451525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11667578549246048168967683 17501367823869072253451525)
                    ·
                      refine ⟨3281506466975451047522161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17501367823869072253451525 3281506466975451047522161)
                      ·
                        rfl

theorem cell23_6390711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 4, 1, 1, 4].length) (baseStart_6390711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6390711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6390711 prefixEnd_6390711 := by exact prefixLift 6390711
  have htrace : WordTrace (prefixWord ++ tailWord_6390711) baseStart_6390711 baseEnd_6390711 := by
    simpa [prefixWord, tailWord_6390711, baseEnd_6390711] using wordTrace_append hprefix tailTrace_6390711
  have hstable : (prefixWord ++ tailWord_6390711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6390711).length < 2 ^ (prefixWord ++ tailWord_6390711).sum := by decide
  have hdescent : baseEnd_6390711 < baseStart_6390711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6390711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6390714 : List Nat := [3, 1, 1, 1, 2, 1, 3, 2, 3, 1, 5]
def baseStart_6390714 : Nat := 118140960795 + 6390714 * 2 ^ 59
def prefixEnd_6390714 : Nat := 4983230072969 + 3 ^ 40 * 6390714 * 2
def baseEnd_6390714 : Nat := 3281508007417414535784647

theorem tailTrace_6390714 : CollatzResearch.WordTrace tailWord_6390714 prefixEnd_6390714 3281508007417414535784647 := by
  unfold tailWord_6390714
  simp only [CollatzResearch.WordTrace]
  refine ⟨58272122142385524975442799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155392325713028066601180797 58272122142385524975442799)
  ·
    refine ⟨87408183213578287463164199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58272122142385524975442799 87408183213578287463164199)
    ·
      refine ⟨131112274820367431194746299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87408183213578287463164199 131112274820367431194746299)
      ·
        refine ⟨196668412230551146792119449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131112274820367431194746299 196668412230551146792119449)
        ·
          refine ⟨147501309172913360094089587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196668412230551146792119449 147501309172913360094089587)
          ·
            refine ⟨221251963759370040141134381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147501309172913360094089587 221251963759370040141134381)
            ·
              refine ⟨82969486409763765052925393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 221251963759370040141134381 82969486409763765052925393)
              ·
                refine ⟨62227114807322823789694045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82969486409763765052925393 62227114807322823789694045)
                ·
                  refine ⟨23335168052746058921135267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62227114807322823789694045 23335168052746058921135267)
                  ·
                    refine ⟨35002752079119088381702901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23335168052746058921135267 35002752079119088381702901)
                    ·
                      refine ⟨3281508007417414535784647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35002752079119088381702901 3281508007417414535784647)
                      ·
                        rfl

theorem cell23_6390714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 3, 1, 5].length) (baseStart_6390714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6390714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6390714 prefixEnd_6390714 := by exact prefixLift 6390714
  have htrace : WordTrace (prefixWord ++ tailWord_6390714) baseStart_6390714 baseEnd_6390714 := by
    simpa [prefixWord, tailWord_6390714, baseEnd_6390714] using wordTrace_append hprefix tailTrace_6390714
  have hstable : (prefixWord ++ tailWord_6390714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6390714).length < 2 ^ (prefixWord ++ tailWord_6390714).sum := by decide
  have hdescent : baseEnd_6390714 < baseStart_6390714 := by decide
  rcases family_descends (prefixWord ++ tailWord_6390714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6390731 : List Nat := [1, 1, 1, 1, 3, 6, 2, 1, 1, 1, 5]
def baseStart_6390731 : Nat := 118140960795 + 6390731 * 2 ^ 59
def prefixEnd_6390731 : Nat := 4983230072969 + 3 ^ 40 * 6390731 * 2
def baseEnd_6390731 : Nat := 3281516736588540969272069

theorem tailTrace_6390731 : CollatzResearch.WordTrace tailWord_6390731 prefixEnd_6390731 3281516736588540969272069 := by
  unfold tailWord_6390731
  simp only [CollatzResearch.WordTrace]
  refine ⟨233089108610480511805140047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155392739073653674536760031 233089108610480511805140047)
  ·
    refine ⟨349633662915720767707710071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233089108610480511805140047 349633662915720767707710071)
    ·
      refine ⟨524450494373581151561565107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349633662915720767707710071 524450494373581151561565107)
      ·
        refine ⟨786675741560371727342347661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 524450494373581151561565107 786675741560371727342347661)
        ·
          refine ⟨295003403085139397753380373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 786675741560371727342347661 295003403085139397753380373)
          ·
            refine ⟨13828284519615909269689705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 295003403085139397753380373 13828284519615909269689705)
            ·
              refine ⟨10371213389711931952267279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13828284519615909269689705 10371213389711931952267279)
              ·
                refine ⟨15556820084567897928400919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10371213389711931952267279 15556820084567897928400919)
                ·
                  refine ⟨23335230126851846892601379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15556820084567897928400919 23335230126851846892601379)
                  ·
                    refine ⟨35002845190277770338902069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23335230126851846892601379 35002845190277770338902069)
                    ·
                      refine ⟨3281516736588540969272069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35002845190277770338902069 3281516736588540969272069)
                      ·
                        rfl

theorem cell23_6390731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 1, 1, 1, 5].length) (baseStart_6390731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6390731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6390731 prefixEnd_6390731 := by exact prefixLift 6390731
  have htrace : WordTrace (prefixWord ++ tailWord_6390731) baseStart_6390731 baseEnd_6390731 := by
    simpa [prefixWord, tailWord_6390731, baseEnd_6390731] using wordTrace_append hprefix tailTrace_6390731
  have hstable : (prefixWord ++ tailWord_6390731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6390731).length < 2 ^ (prefixWord ++ tailWord_6390731).sum := by decide
  have hdescent : baseEnd_6390731 < baseStart_6390731 := by decide
  rcases family_descends (prefixWord ++ tailWord_6390731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6390734 : List Nat := [4, 1, 1, 1, 2, 3, 11]
def baseStart_6390734 : Nat := 118140960795 + 6390734 * 2 ^ 59
def prefixEnd_6390734 : Nat := 4983230072969 + 3 ^ 40 * 6390734 * 2
def baseEnd_6390734 : Nat := 40512571321364252562155

theorem tailTrace_6390734 : CollatzResearch.WordTrace tailWord_6390734 prefixEnd_6390734 40512571321364252562155 := by
  unfold tailWord_6390734
  simp only [CollatzResearch.WordTrace]
  refine ⟨29136152253683705414687407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155392812019646428878332837 29136152253683705414687407)
  ·
    refine ⟨43704228380525558122031111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29136152253683705414687407 43704228380525558122031111)
    ·
      refine ⟨65556342570788337183046667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43704228380525558122031111 65556342570788337183046667)
      ·
        refine ⟨98334513856182505774570001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65556342570788337183046667 98334513856182505774570001)
        ·
          refine ⟨73750885392136879330927501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98334513856182505774570001 73750885392136879330927501)
          ·
            refine ⟨27656582022051329749097813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73750885392136879330927501 27656582022051329749097813)
            ·
              refine ⟨40512571321364252562155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 27656582022051329749097813 40512571321364252562155)
              ·
                rfl

theorem cell23_6390734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 11].length) (baseStart_6390734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6390734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6390734 prefixEnd_6390734 := by exact prefixLift 6390734
  have htrace : WordTrace (prefixWord ++ tailWord_6390734) baseStart_6390734 baseEnd_6390734 := by
    simpa [prefixWord, tailWord_6390734, baseEnd_6390734] using wordTrace_append hprefix tailTrace_6390734
  have hstable : (prefixWord ++ tailWord_6390734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6390734).length < 2 ^ (prefixWord ++ tailWord_6390734).sum := by decide
  have hdescent : baseEnd_6390734 < baseStart_6390734 := by decide
  rcases family_descends (prefixWord ++ tailWord_6390734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6390738 : List Nat := [3, 2, 2, 3, 1, 1, 2, 1, 4, 4]
def baseStart_6390738 : Nat := 118140960795 + 6390738 * 2 ^ 59
def prefixEnd_6390738 : Nat := 4983230072969 + 3 ^ 40 * 6390738 * 2
def baseEnd_6390738 : Nat := 1093840110317707480628179

theorem tailTrace_6390738 : CollatzResearch.WordTrace tailWord_6390738 prefixEnd_6390738 1093840110317707480628179 := by
  unfold tailWord_6390738
  simp only [CollatzResearch.WordTrace]
  refine ⟨58272340980363788000161217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155392909280970101333763245 58272340980363788000161217)
  ·
    refine ⟨43704255735272841000120913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58272340980363788000161217 43704255735272841000120913)
    ·
      refine ⟨32778191801454630750090685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43704255735272841000120913 32778191801454630750090685)
      ·
        refine ⟨12291821925545486531284007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32778191801454630750090685 12291821925545486531284007)
        ·
          refine ⟨18437732888318229796926011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12291821925545486531284007 18437732888318229796926011)
          ·
            refine ⟨27656599332477344695389017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18437732888318229796926011 27656599332477344695389017)
            ·
              refine ⟨20742449499358008521541763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27656599332477344695389017 20742449499358008521541763)
              ·
                refine ⟨31113674249037012782312645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20742449499358008521541763 31113674249037012782312645)
                ·
                  refine ⟨5833813921694439896683621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31113674249037012782312645 5833813921694439896683621)
                  ·
                    refine ⟨1093840110317707480628179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5833813921694439896683621 1093840110317707480628179)
                    ·
                      rfl

theorem cell23_6390738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_6390738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6390738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6390738 prefixEnd_6390738 := by exact prefixLift 6390738
  have htrace : WordTrace (prefixWord ++ tailWord_6390738) baseStart_6390738 baseEnd_6390738 := by
    simpa [prefixWord, tailWord_6390738, baseEnd_6390738] using wordTrace_append hprefix tailTrace_6390738
  have hstable : (prefixWord ++ tailWord_6390738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6390738).length < 2 ^ (prefixWord ++ tailWord_6390738).sum := by decide
  have hdescent : baseEnd_6390738 < baseStart_6390738 := by decide
  rcases family_descends (prefixWord ++ tailWord_6390738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6390745 : List Nat := [1, 2, 1, 2, 5, 1, 3, 1, 3, 2, 2]
def baseStart_6390745 : Nat := 118140960795 + 6390745 * 2 ^ 59
def prefixEnd_6390745 : Nat := 4983230072969 + 3 ^ 40 * 6390745 * 2
def baseEnd_6390745 : Nat := 3281523925317703914497005

theorem tailTrace_6390745 : CollatzResearch.WordTrace tailWord_6390745 prefixEnd_6390745 3281523925317703914497005 := by
  unfold tailWord_6390745
  simp only [CollatzResearch.WordTrace]
  refine ⟨233089619232429792196149689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155393079488286528130766459 233089619232429792196149689)
  ·
    refine ⟨174817214424322344147112267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233089619232429792196149689 174817214424322344147112267)
    ·
      refine ⟨262225821636483516220668401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174817214424322344147112267 262225821636483516220668401)
      ·
        refine ⟨196669366227362637165501301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262225821636483516220668401 196669366227362637165501301)
        ·
          refine ⟨18437753083815247234265747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 196669366227362637165501301 18437753083815247234265747)
          ·
            refine ⟨27656629625722870851398621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18437753083815247234265747 27656629625722870851398621)
            ·
              refine ⟨10371236109646076569274483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27656629625722870851398621 10371236109646076569274483)
              ·
                refine ⟨15556854164469114853911725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10371236109646076569274483 15556854164469114853911725)
                ·
                  refine ⟨5833820311675918070216897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15556854164469114853911725 5833820311675918070216897)
                  ·
                    refine ⟨4375365233756938552662673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5833820311675918070216897 4375365233756938552662673)
                    ·
                      refine ⟨3281523925317703914497005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4375365233756938552662673 3281523925317703914497005)
                      ·
                        rfl

theorem cell23_6390745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 1, 3, 2, 2].length) (baseStart_6390745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6390745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6390745 prefixEnd_6390745 := by exact prefixLift 6390745
  have htrace : WordTrace (prefixWord ++ tailWord_6390745) baseStart_6390745 baseEnd_6390745 := by
    simpa [prefixWord, tailWord_6390745, baseEnd_6390745] using wordTrace_append hprefix tailTrace_6390745
  have hstable : (prefixWord ++ tailWord_6390745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6390745).length < 2 ^ (prefixWord ++ tailWord_6390745).sum := by decide
  have hdescent : baseEnd_6390745 < baseStart_6390745 := by decide
  rcases family_descends (prefixWord ++ tailWord_6390745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6390751 : List Nat := [1, 1, 2, 3, 5, 1, 2, 8]
def baseStart_6390751 : Nat := 118140960795 + 6390751 * 2 ^ 59
def prefixEnd_6390751 : Nat := 4983230072969 + 3 ^ 40 * 6390751 * 2
def baseEnd_6390751 : Nat := 121538037266727070037851

theorem tailTrace_6390751 : CollatzResearch.WordTrace tailWord_6390751 prefixEnd_6390751 121538037266727070037851 := by
  unfold tailWord_6390751
  simp only [CollatzResearch.WordTrace]
  refine ⟨233089838070408055220868107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155393225380272036813912071 233089838070408055220868107)
  ·
    refine ⟨349634757105612082831302161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233089838070408055220868107 349634757105612082831302161)
    ·
      refine ⟨262226067829209062123476621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 349634757105612082831302161 262226067829209062123476621)
      ·
        refine ⟨98334775435953398296303733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 262226067829209062123476621 98334775435953398296303733)
        ·
          refine ⟨9218885197120631090278475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 98334775435953398296303733 9218885197120631090278475)
          ·
            refine ⟨13828327795680946635417713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9218885197120631090278475 13828327795680946635417713)
            ·
              refine ⟨10371245846760709976563285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13828327795680946635417713 10371245846760709976563285)
              ·
                refine ⟨121538037266727070037851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10371245846760709976563285 121538037266727070037851)
                ·
                  rfl

theorem cell23_6390751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 8].length) (baseStart_6390751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6390751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6390751 prefixEnd_6390751 := by exact prefixLift 6390751
  have htrace : WordTrace (prefixWord ++ tailWord_6390751) baseStart_6390751 baseEnd_6390751 := by
    simpa [prefixWord, tailWord_6390751, baseEnd_6390751] using wordTrace_append hprefix tailTrace_6390751
  have hstable : (prefixWord ++ tailWord_6390751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6390751).length < 2 ^ (prefixWord ++ tailWord_6390751).sum := by decide
  have hdescent : baseEnd_6390751 < baseStart_6390751 := by decide
  rcases family_descends (prefixWord ++ tailWord_6390751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6390782 : List Nat := [4, 2, 2, 2, 3, 1, 1, 1, 1, 1, 5]
def baseStart_6390782 : Nat := 118140960795 + 6390782 * 2 ^ 59
def prefixEnd_6390782 : Nat := 4983230072969 + 3 ^ 40 * 6390782 * 2
def baseEnd_6390782 : Nat := 3281542924101920269734335

theorem tailTrace_6390782 : CollatzResearch.WordTrace tailWord_6390782 prefixEnd_6390782 3281542924101920269734335 := by
  unfold tailWord_6390782
  simp only [CollatzResearch.WordTrace]
  refine ⟨29136371091661968439405825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155393979155530498343497733 29136371091661968439405825)
  ·
    refine ⟨21852278318746476329554369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29136371091661968439405825 21852278318746476329554369)
    ·
      refine ⟨16389208739059857247165777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21852278318746476329554369 16389208739059857247165777)
      ·
        refine ⟨12291906554294892935374333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16389208739059857247165777 12291906554294892935374333)
        ·
          refine ⟨4609464957860584850765375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12291906554294892935374333 4609464957860584850765375)
          ·
            refine ⟨6914197436790877276148063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4609464957860584850765375 6914197436790877276148063)
            ·
              refine ⟨10371296155186315914222095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6914197436790877276148063 10371296155186315914222095)
              ·
                refine ⟨15556944232779473871333143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10371296155186315914222095 15556944232779473871333143)
                ·
                  refine ⟨23335416349169210806999715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15556944232779473871333143 23335416349169210806999715)
                  ·
                    refine ⟨35003124523753816210499573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23335416349169210806999715 35003124523753816210499573)
                    ·
                      refine ⟨3281542924101920269734335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35003124523753816210499573 3281542924101920269734335)
                      ·
                        rfl

theorem cell23_6390782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_6390782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6390782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6390782 prefixEnd_6390782 := by exact prefixLift 6390782
  have htrace : WordTrace (prefixWord ++ tailWord_6390782) baseStart_6390782 baseEnd_6390782 := by
    simpa [prefixWord, tailWord_6390782, baseEnd_6390782] using wordTrace_append hprefix tailTrace_6390782
  have hstable : (prefixWord ++ tailWord_6390782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6390782).length < 2 ^ (prefixWord ++ tailWord_6390782).sum := by decide
  have hdescent : baseEnd_6390782 < baseStart_6390782 := by decide
  rcases family_descends (prefixWord ++ tailWord_6390782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6390795 : List Nat := [1, 1, 1, 1, 6, 3, 2, 2, 2, 1, 3]
def baseStart_6390795 : Nat := 118140960795 + 6390795 * 2 ^ 59
def prefixEnd_6390795 : Nat := 4983230072969 + 3 ^ 40 * 6390795 * 2
def baseEnd_6390795 : Nat := 3281549599350428718871775

theorem tailTrace_6390795 : CollatzResearch.WordTrace tailWord_6390795 prefixEnd_6390795 3281549599350428718871775 := by
  unfold tailWord_6390795
  simp only [CollatzResearch.WordTrace]
  refine ⟨233091442882248650735469839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155394295254832433823646559 233091442882248650735469839)
  ·
    refine ⟨349637164323372976103204759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233091442882248650735469839 349637164323372976103204759)
    ·
      refine ⟨524455746485059464154807139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349637164323372976103204759 524455746485059464154807139)
      ·
        refine ⟨786683619727589196232210709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 524455746485059464154807139 786683619727589196232210709)
        ·
          refine ⟨36875794674730743573384877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 786683619727589196232210709 36875794674730743573384877)
          ·
            refine ⟨13828423003024028840019329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36875794674730743573384877 13828423003024028840019329)
            ·
              refine ⟨10371317252268021630014497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13828423003024028840019329 10371317252268021630014497)
              ·
                refine ⟨7778487939201016222510873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10371317252268021630014497 7778487939201016222510873)
                ·
                  refine ⟨5833865954400762166883155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7778487939201016222510873 5833865954400762166883155)
                  ·
                    refine ⟨8750798931601143250324733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5833865954400762166883155 8750798931601143250324733)
                    ·
                      refine ⟨3281549599350428718871775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8750798931601143250324733 3281549599350428718871775)
                      ·
                        rfl

theorem cell23_6390795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 2, 2, 1, 3].length) (baseStart_6390795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6390795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6390795 prefixEnd_6390795 := by exact prefixLift 6390795
  have htrace : WordTrace (prefixWord ++ tailWord_6390795) baseStart_6390795 baseEnd_6390795 := by
    simpa [prefixWord, tailWord_6390795, baseEnd_6390795] using wordTrace_append hprefix tailTrace_6390795
  have hstable : (prefixWord ++ tailWord_6390795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6390795).length < 2 ^ (prefixWord ++ tailWord_6390795).sum := by decide
  have hdescent : baseEnd_6390795 < baseStart_6390795 := by decide
  rcases family_descends (prefixWord ++ tailWord_6390795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6390802 : List Nat := [3, 2, 5, 1, 1, 2, 1, 8]
def baseStart_6390802 : Nat := 118140960795 + 6390802 * 2 ^ 59
def prefixEnd_6390802 : Nat := 4983230072969 + 3 ^ 40 * 6390802 * 2
def baseEnd_6390802 : Nat := 121539007174630007092009

theorem tailTrace_6390802 : CollatzResearch.WordTrace tailWord_6390802 prefixEnd_6390802 121539007174630007092009 := by
  unfold tailWord_6390802
  simp only [CollatzResearch.WordTrace]
  refine ⟨58272924548305822732743665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155394465462148860620649773 58272924548305822732743665)
  ·
    refine ⟨43704693411229367049557749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58272924548305822732743665 43704693411229367049557749)
    ·
      refine ⟨4097315007302753160896039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43704693411229367049557749 4097315007302753160896039)
      ·
        refine ⟨6145972510954129741344059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4097315007302753160896039 6145972510954129741344059)
        ·
          refine ⟨9218958766431194612016089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6145972510954129741344059 9218958766431194612016089)
          ·
            refine ⟨6914219074823395959012067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9218958766431194612016089 6914219074823395959012067)
            ·
              refine ⟨10371328612235093938518101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6914219074823395959012067 10371328612235093938518101)
              ·
                refine ⟨121539007174630007092009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10371328612235093938518101 121539007174630007092009)
                ·
                  rfl

theorem cell23_6390802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 8].length) (baseStart_6390802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6390802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6390802 prefixEnd_6390802 := by exact prefixLift 6390802
  have htrace : WordTrace (prefixWord ++ tailWord_6390802) baseStart_6390802 baseEnd_6390802 := by
    simpa [prefixWord, tailWord_6390802, baseEnd_6390802] using wordTrace_append hprefix tailTrace_6390802
  have hstable : (prefixWord ++ tailWord_6390802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6390802).length < 2 ^ (prefixWord ++ tailWord_6390802).sum := by decide
  have hdescent : baseEnd_6390802 < baseStart_6390802 := by decide
  rcases family_descends (prefixWord ++ tailWord_6390802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6390821 : List Nat := [1, 3, 1, 2, 2, 2, 1, 2, 2, 4, 3]
def baseStart_6390821 : Nat := 118140960795 + 6390821 * 2 ^ 59
def prefixEnd_6390821 : Nat := 4983230072969 + 3 ^ 40 * 6390821 * 2
def baseEnd_6390821 : Nat := 3281562949847445617146655

theorem tailTrace_6390821 : CollatzResearch.WordTrace tailWord_6390821 prefixEnd_6390821 3281562949847445617146655 := by
  unfold tailWord_6390821
  simp only [CollatzResearch.WordTrace]
  refine ⟨233092391180154457175916317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155394927453436304783944211 233092391180154457175916317)
  ·
    refine ⟨87409646692557921440968619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233092391180154457175916317 87409646692557921440968619)
    ·
      refine ⟨131114470038836882161452929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87409646692557921440968619 131114470038836882161452929)
      ·
        refine ⟨98335852529127661621089697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131114470038836882161452929 98335852529127661621089697)
        ·
          refine ⟨73751889396845746215817273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98335852529127661621089697 73751889396845746215817273)
          ·
            refine ⟨55313917047634309661862955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73751889396845746215817273 55313917047634309661862955)
            ·
              refine ⟨82970875571451464492794433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55313917047634309661862955 82970875571451464492794433)
              ·
                refine ⟨62228156678588598369595825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82970875571451464492794433 62228156678588598369595825)
                ·
                  refine ⟨46671117508941448777196869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62228156678588598369595825 46671117508941448777196869)
                  ·
                    refine ⟨8750834532926521645724413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46671117508941448777196869 8750834532926521645724413)
                    ·
                      refine ⟨3281562949847445617146655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8750834532926521645724413 3281562949847445617146655)
                      ·
                        rfl

theorem cell23_6390821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 4, 3].length) (baseStart_6390821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6390821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6390821 prefixEnd_6390821 := by exact prefixLift 6390821
  have htrace : WordTrace (prefixWord ++ tailWord_6390821) baseStart_6390821 baseEnd_6390821 := by
    simpa [prefixWord, tailWord_6390821, baseEnd_6390821] using wordTrace_append hprefix tailTrace_6390821
  have hstable : (prefixWord ++ tailWord_6390821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6390821).length < 2 ^ (prefixWord ++ tailWord_6390821).sum := by decide
  have hdescent : baseEnd_6390821 < baseStart_6390821 := by decide
  rcases family_descends (prefixWord ++ tailWord_6390821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6390851 : List Nat := [1, 1, 1, 3, 1, 2, 3, 1, 4, 3, 3]
def baseStart_6390851 : Nat := 118140960795 + 6390851 * 2 ^ 59
def prefixEnd_6390851 : Nat := 4983230072969 + 3 ^ 40 * 6390851 * 2
def baseEnd_6390851 : Nat := 3281578354267080499771517

theorem tailTrace_6390851 : CollatzResearch.WordTrace tailWord_6390851 prefixEnd_6390851 3281578354267080499771517 := by
  unfold tailWord_6390851
  simp only [CollatzResearch.WordTrace]
  refine ⟨233093485370045772299508407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155395656913363848199672271 233093485370045772299508407)
  ·
    refine ⟨349640228055068658449262611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233093485370045772299508407 349640228055068658449262611)
    ·
      refine ⟨524460342082602987673893917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349640228055068658449262611 524460342082602987673893917)
      ·
        refine ⟨196672628280976120377710219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 524460342082602987673893917 196672628280976120377710219)
        ·
          refine ⟨295008942421464180566565329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196672628280976120377710219 295008942421464180566565329)
          ·
            refine ⟨221256706816098135424923997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295008942421464180566565329 221256706816098135424923997)
            ·
              refine ⟨82971265056036800784346499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 221256706816098135424923997 82971265056036800784346499)
              ·
                refine ⟨124456897584055201176519749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82971265056036800784346499 124456897584055201176519749)
                ·
                  refine ⟨23335668297010350220597453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 124456897584055201176519749 23335668297010350220597453)
                  ·
                    refine ⟨8750875611378881332724045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23335668297010350220597453 8750875611378881332724045)
                    ·
                      refine ⟨3281578354267080499771517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8750875611378881332724045 3281578354267080499771517)
                      ·
                        rfl

theorem cell23_6390851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4, 3, 3].length) (baseStart_6390851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6390851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6390851 prefixEnd_6390851 := by exact prefixLift 6390851
  have htrace : WordTrace (prefixWord ++ tailWord_6390851) baseStart_6390851 baseEnd_6390851 := by
    simpa [prefixWord, tailWord_6390851, baseEnd_6390851] using wordTrace_append hprefix tailTrace_6390851
  have hstable : (prefixWord ++ tailWord_6390851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6390851).length < 2 ^ (prefixWord ++ tailWord_6390851).sum := by decide
  have hdescent : baseEnd_6390851 < baseStart_6390851 := by decide
  rcases family_descends (prefixWord ++ tailWord_6390851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6390858 : List Nat := [3, 1, 2, 1, 1, 2, 4, 4, 5]
def baseStart_6390858 : Nat := 118140960795 + 6390858 * 2 ^ 59
def prefixEnd_6390858 : Nat := 4983230072969 + 3 ^ 40 * 6390858 * 2
def baseEnd_6390858 : Nat := 364620216514629108042665

theorem tailTrace_6390858 : CollatzResearch.WordTrace tailWord_6390858 prefixEnd_6390858 364620216514629108042665 := by
  unfold tailWord_6390858
  simp only [CollatzResearch.WordTrace]
  refine ⟨58273435170255103123753307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155395827120680274996675485 58273435170255103123753307)
  ·
    refine ⟨87410152755382654685629961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58273435170255103123753307 87410152755382654685629961)
    ·
      refine ⟨65557614566536991014222471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87410152755382654685629961 65557614566536991014222471)
      ·
        refine ⟨98336421849805486521333707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65557614566536991014222471 98336421849805486521333707)
        ·
          refine ⟨147504632774708229782000561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98336421849805486521333707 147504632774708229782000561)
          ·
            refine ⟨110628474581031172336500421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147504632774708229782000561 110628474581031172336500421)
            ·
              refine ⟨20742838983943344813093829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110628474581031172336500421 20742838983943344813093829)
              ·
                refine ⟨3889282309489377152455093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20742838983943344813093829 3889282309489377152455093)
                ·
                  refine ⟨364620216514629108042665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3889282309489377152455093 364620216514629108042665)
                  ·
                    rfl

theorem cell23_6390858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 4, 5].length) (baseStart_6390858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6390858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6390858 prefixEnd_6390858 := by exact prefixLift 6390858
  have htrace : WordTrace (prefixWord ++ tailWord_6390858) baseStart_6390858 baseEnd_6390858 := by
    simpa [prefixWord, tailWord_6390858, baseEnd_6390858] using wordTrace_append hprefix tailTrace_6390858
  have hstable : (prefixWord ++ tailWord_6390858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6390858).length < 2 ^ (prefixWord ++ tailWord_6390858).sum := by decide
  have hdescent : baseEnd_6390858 < baseStart_6390858 := by decide
  rcases family_descends (prefixWord ++ tailWord_6390858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6390868 : List Nat := [2, 4, 1, 1, 1, 1, 4, 1, 2, 3, 3]
def baseStart_6390868 : Nat := 118140960795 + 6390868 * 2 ^ 59
def prefixEnd_6390868 : Nat := 4983230072969 + 3 ^ 40 * 6390868 * 2
def baseEnd_6390868 : Nat := 3281587083438206933258939

theorem tailTrace_6390868 : CollatzResearch.WordTrace tailWord_6390868 prefixEnd_6390868 3281587083438206933258939 := by
  unfold tailWord_6390868
  simp only [CollatzResearch.WordTrace]
  refine ⟨116547052705492092101438629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155396070273989456135251505 116547052705492092101438629)
  ·
    refine ⟨21852572382279767269019743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116547052705492092101438629 21852572382279767269019743)
    ·
      refine ⟨32778858573419650903529615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21852572382279767269019743 32778858573419650903529615)
      ·
        refine ⟨49168287860129476355294423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32778858573419650903529615 49168287860129476355294423)
        ·
          refine ⟨73752431790194214532941635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49168287860129476355294423 73752431790194214532941635)
          ·
            refine ⟨110628647685291321799412453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73752431790194214532941635 110628647685291321799412453)
            ·
              refine ⟨20742871440992122837389835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110628647685291321799412453 20742871440992122837389835)
              ·
                refine ⟨31114307161488184256084753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20742871440992122837389835 31114307161488184256084753)
                ·
                  refine ⟨23335730371116138192063565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31114307161488184256084753 23335730371116138192063565)
                  ·
                    refine ⟨8750898889168551822023837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23335730371116138192063565 8750898889168551822023837)
                    ·
                      refine ⟨3281587083438206933258939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8750898889168551822023837 3281587083438206933258939)
                      ·
                        rfl

theorem cell23_6390868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_6390868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6390868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6390868 prefixEnd_6390868 := by exact prefixLift 6390868
  have htrace : WordTrace (prefixWord ++ tailWord_6390868) baseStart_6390868 baseEnd_6390868 := by
    simpa [prefixWord, tailWord_6390868, baseEnd_6390868] using wordTrace_append hprefix tailTrace_6390868
  have hstable : (prefixWord ++ tailWord_6390868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6390868).length < 2 ^ (prefixWord ++ tailWord_6390868).sum := by decide
  have hdescent : baseEnd_6390868 < baseStart_6390868 := by decide
  rcases family_descends (prefixWord ++ tailWord_6390868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6390891 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 8, 1, 4]
def baseStart_6390891 : Nat := 118140960795 + 6390891 * 2 ^ 59
def prefixEnd_6390891 : Nat := 4983230072969 + 3 ^ 40 * 6390891 * 2
def baseEnd_6390891 : Nat := 3281598893493260343271333

theorem tailTrace_6390891 : CollatzResearch.WordTrace tailWord_6390891 prefixEnd_6390891 3281598893493260343271333 := by
  unfold tailWord_6390891
  simp only [CollatzResearch.WordTrace]
  refine ⟨233094944289900859130964527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155396629526600572753976351 233094944289900859130964527)
  ·
    refine ⟨349642416434851288696446791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233094944289900859130964527 349642416434851288696446791)
    ·
      refine ⟨524463624652276933044670187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349642416434851288696446791 524463624652276933044670187)
      ·
        refine ⟨786695436978415399567005281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 524463624652276933044670187 786695436978415399567005281)
        ·
          refine ⟨590021577733811549675253961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 786695436978415399567005281 590021577733811549675253961)
          ·
            refine ⟨442516183300358662256440471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 590021577733811549675253961 442516183300358662256440471)
            ·
              refine ⟨663774274950537993384660707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 442516183300358662256440471 663774274950537993384660707)
              ·
                refine ⟨995661412425806990076991061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 663774274950537993384660707 995661412425806990076991061)
                ·
                  refine ⟨11667907176864925664964739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 995661412425806990076991061 11667907176864925664964739)
                  ·
                    refine ⟨17501860765297388497447109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11667907176864925664964739 17501860765297388497447109)
                    ·
                      refine ⟨3281598893493260343271333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17501860765297388497447109 3281598893493260343271333)
                      ·
                        rfl

theorem cell23_6390891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 8, 1, 4].length) (baseStart_6390891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6390891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6390891 prefixEnd_6390891 := by exact prefixLift 6390891
  have htrace : WordTrace (prefixWord ++ tailWord_6390891) baseStart_6390891 baseEnd_6390891 := by
    simpa [prefixWord, tailWord_6390891, baseEnd_6390891] using wordTrace_append hprefix tailTrace_6390891
  have hstable : (prefixWord ++ tailWord_6390891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6390891).length < 2 ^ (prefixWord ++ tailWord_6390891).sum := by decide
  have hdescent : baseEnd_6390891 < baseStart_6390891 := by decide
  rcases family_descends (prefixWord ++ tailWord_6390891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6390908 : List Nat := [2, 2, 2, 1, 1, 3, 3, 2, 2, 1, 4]
def baseStart_6390908 : Nat := 118140960795 + 6390908 * 2 ^ 59
def prefixEnd_6390908 : Nat := 4983230072969 + 3 ^ 40 * 6390908 * 2
def baseEnd_6390908 : Nat := 3281607622664386776758755

theorem tailTrace_6390908 : CollatzResearch.WordTrace tailWord_6390908 prefixEnd_6390908 3281607622664386776758755 := by
  unfold tailWord_6390908
  simp only [CollatzResearch.WordTrace]
  refine ⟨116547782165419635517166689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155397042887226180689555585 116547782165419635517166689)
  ·
    refine ⟨87410836624064726637875017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116547782165419635517166689 87410836624064726637875017)
    ·
      refine ⟨65558127468048544978406263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87410836624064726637875017 65558127468048544978406263)
      ·
        refine ⟨98337191202072817467609395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65558127468048544978406263 98337191202072817467609395)
        ·
          refine ⟨147505786803109226201414093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98337191202072817467609395 147505786803109226201414093)
          ·
            refine ⟨55314670051165959825530285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147505786803109226201414093 55314670051165959825530285)
            ·
              refine ⟨20743001269187234934573857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55314670051165959825530285 20743001269187234934573857)
              ·
                refine ⟨15557250951890426200930393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20743001269187234934573857 15557250951890426200930393)
                ·
                  refine ⟨11667938213917819650697795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15557250951890426200930393 11667938213917819650697795)
                  ·
                    refine ⟨17501907320876729476046693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11667938213917819650697795 17501907320876729476046693)
                    ·
                      refine ⟨3281607622664386776758755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17501907320876729476046693 3281607622664386776758755)
                      ·
                        rfl

theorem cell23_6390908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 2, 2, 1, 4].length) (baseStart_6390908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6390908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6390908 prefixEnd_6390908 := by exact prefixLift 6390908
  have htrace : WordTrace (prefixWord ++ tailWord_6390908) baseStart_6390908 baseEnd_6390908 := by
    simpa [prefixWord, tailWord_6390908, baseEnd_6390908] using wordTrace_append hprefix tailTrace_6390908
  have hstable : (prefixWord ++ tailWord_6390908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6390908).length < 2 ^ (prefixWord ++ tailWord_6390908).sum := by decide
  have hdescent : baseEnd_6390908 < baseStart_6390908 := by decide
  rcases family_descends (prefixWord ++ tailWord_6390908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6390911 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 2, 8, 3]
def baseStart_6390911 : Nat := 118140960795 + 6390911 * 2 ^ 59
def prefixEnd_6390911 : Nat := 4983230072969 + 3 ^ 40 * 6390911 * 2
def baseEnd_6390911 : Nat := 3281609163106350265021241

theorem tailTrace_6390911 : CollatzResearch.WordTrace tailWord_6390911 prefixEnd_6390911 3281609163106350265021241 := by
  unfold tailWord_6390911
  simp only [CollatzResearch.WordTrace]
  refine ⟨233095673749828402546692587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155397115833218935031128391 233095673749828402546692587)
  ·
    refine ⟨349643510624742603820038881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233095673749828402546692587 349643510624742603820038881)
    ·
      refine ⟨262232632968556952865029161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 349643510624742603820038881 262232632968556952865029161)
      ·
        refine ⟨196674474726417714648771871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262232632968556952865029161 196674474726417714648771871)
        ·
          refine ⟨295011712089626571973157807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196674474726417714648771871 295011712089626571973157807)
          ·
            refine ⟨442517568134439857959736711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295011712089626571973157807 442517568134439857959736711)
            ·
              refine ⟨663776352201659786939605067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 442517568134439857959736711 663776352201659786939605067)
              ·
                refine ⟨995664528302489680409407601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 663776352201659786939605067 995664528302489680409407601)
                ·
                  refine ⟨746748396226867260307055701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 995664528302489680409407601 746748396226867260307055701)
                  ·
                    refine ⟨8750957768283600706723309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 746748396226867260307055701 8750957768283600706723309)
                    ·
                      refine ⟨3281609163106350265021241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8750957768283600706723309 3281609163106350265021241)
                      ·
                        rfl

theorem cell23_6390911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 8, 3].length) (baseStart_6390911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6390911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6390911 prefixEnd_6390911 := by exact prefixLift 6390911
  have htrace : WordTrace (prefixWord ++ tailWord_6390911) baseStart_6390911 baseEnd_6390911 := by
    simpa [prefixWord, tailWord_6390911, baseEnd_6390911] using wordTrace_append hprefix tailTrace_6390911
  have hstable : (prefixWord ++ tailWord_6390911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6390911).length < 2 ^ (prefixWord ++ tailWord_6390911).sum := by decide
  have hdescent : baseEnd_6390911 < baseStart_6390911 := by decide
  rcases family_descends (prefixWord ++ tailWord_6390911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6390942 : List Nat := [4, 3, 1, 1, 2, 2, 2, 1, 2, 1, 4]
def baseStart_6390942 : Nat := 118140960795 + 6390942 * 2 ^ 59
def prefixEnd_6390942 : Nat := 4983230072969 + 3 ^ 40 * 6390942 * 2
def baseEnd_6390942 : Nat := 3281625081006639643733599

theorem tailTrace_6390942 : CollatzResearch.WordTrace tailWord_6390942 prefixEnd_6390942 3281625081006639643733599 := by
  unfold tailWord_6390942
  simp only [CollatzResearch.WordTrace]
  refine ⟨29137100551589511855133885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155397869608477396560714053 29137100551589511855133885)
  ·
    refine ⟨10926412706846066945675207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29137100551589511855133885 10926412706846066945675207)
    ·
      refine ⟨16389619060269100418512811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10926412706846066945675207 16389619060269100418512811)
      ·
        refine ⟨24584428590403650627769217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16389619060269100418512811 24584428590403650627769217)
        ·
          refine ⟨18438321442802737970826913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24584428590403650627769217 18438321442802737970826913)
          ·
            refine ⟨13828741082102053478120185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18438321442802737970826913 13828741082102053478120185)
            ·
              refine ⟨10371555811576540108590139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13828741082102053478120185 10371555811576540108590139)
              ·
                refine ⟨15557333717364810162885209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10371555811576540108590139 15557333717364810162885209)
                ·
                  refine ⟨11668000288023607622163907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15557333717364810162885209 11668000288023607622163907)
                  ·
                    refine ⟨17502000432035411433245861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11668000288023607622163907 17502000432035411433245861)
                    ·
                      refine ⟨3281625081006639643733599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17502000432035411433245861 3281625081006639643733599)
                      ·
                        rfl

theorem cell23_6390942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_6390942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6390942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6390942 prefixEnd_6390942 := by exact prefixLift 6390942
  have htrace : WordTrace (prefixWord ++ tailWord_6390942) baseStart_6390942 baseEnd_6390942 := by
    simpa [prefixWord, tailWord_6390942, baseEnd_6390942] using wordTrace_append hprefix tailTrace_6390942
  have hstable : (prefixWord ++ tailWord_6390942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6390942).length < 2 ^ (prefixWord ++ tailWord_6390942).sum := by decide
  have hdescent : baseEnd_6390942 < baseStart_6390942 := by decide
  rcases family_descends (prefixWord ++ tailWord_6390942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6390945 : List Nat := [1, 2, 3, 3, 1, 1, 4, 1, 2, 2, 3]
def baseStart_6390945 : Nat := 118140960795 + 6390945 * 2 ^ 59
def prefixEnd_6390945 : Nat := 4983230072969 + 3 ^ 40 * 6390945 * 2
def baseEnd_6390945 : Nat := 3281626621448603131996085

theorem tailTrace_6390945 : CollatzResearch.WordTrace tailWord_6390945 prefixEnd_6390945 3281626621448603131996085 := by
  unfold tailWord_6390945
  simp only [CollatzResearch.WordTrace]
  refine ⟨233096913831705226353430289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155397942554470150902286859 233096913831705226353430289)
  ·
    refine ⟨174822685373778919765072717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233096913831705226353430289 174822685373778919765072717)
    ·
      refine ⟨65558507015167094911902269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174822685373778919765072717 65558507015167094911902269)
      ·
        refine ⟨24584440130687660591963351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65558507015167094911902269 24584440130687660591963351)
        ·
          refine ⟨36876660196031490887945027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24584440130687660591963351 36876660196031490887945027)
          ·
            refine ⟨55314990294047236331917541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36876660196031490887945027 55314990294047236331917541)
            ·
              refine ⟨10371560680133856812234539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55314990294047236331917541 10371560680133856812234539)
              ·
                refine ⟨15557341020200785218351809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10371560680133856812234539 15557341020200785218351809)
                ·
                  refine ⟨11668005765150588913763857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15557341020200785218351809 11668005765150588913763857)
                  ·
                    refine ⟨8751004323862941685322893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11668005765150588913763857 8751004323862941685322893)
                    ·
                      refine ⟨3281626621448603131996085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8751004323862941685322893 3281626621448603131996085)
                      ·
                        rfl

theorem cell23_6390945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_6390945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6390945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6390945 prefixEnd_6390945 := by exact prefixLift 6390945
  have htrace : WordTrace (prefixWord ++ tailWord_6390945) baseStart_6390945 baseEnd_6390945 := by
    simpa [prefixWord, tailWord_6390945, baseEnd_6390945] using wordTrace_append hprefix tailTrace_6390945
  have hstable : (prefixWord ++ tailWord_6390945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6390945).length < 2 ^ (prefixWord ++ tailWord_6390945).sum := by decide
  have hdescent : baseEnd_6390945 < baseStart_6390945 := by decide
  rcases family_descends (prefixWord ++ tailWord_6390945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6390969 : List Nat := [1, 2, 1, 4, 1, 5, 2, 2, 1, 4]
def baseStart_6390969 : Nat := 118140960795 + 6390969 * 2 ^ 59
def prefixEnd_6390969 : Nat := 4983230072969 + 3 ^ 40 * 6390969 * 2
def baseEnd_6390969 : Nat := 1093879648328103679365325

theorem tailTrace_6390969 : CollatzResearch.WordTrace tailWord_6390969 prefixEnd_6390969 1093879648328103679365325 := by
  unfold tailWord_6390969
  simp only [CollatzResearch.WordTrace]
  refine ⟨233097789183618278452303961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155398526122412185634869307 233097789183618278452303961)
  ·
    refine ⟨174823341887713708839227971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233097789183618278452303961 174823341887713708839227971)
    ·
      refine ⟨262235012831570563258841957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174823341887713708839227971 262235012831570563258841957)
      ·
        refine ⟨49169064905919480611032867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 262235012831570563258841957 49169064905919480611032867)
        ·
          refine ⟨73753597358879220916549301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49169064905919480611032867 73753597358879220916549301)
          ·
            refine ⟨6914399752394926960926497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73753597358879220916549301 6914399752394926960926497)
            ·
              refine ⟨5185799814296195220694873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6914399752394926960926497 5185799814296195220694873)
              ·
                refine ⟨3889349860722146415521155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5185799814296195220694873 3889349860722146415521155)
                ·
                  refine ⟨5834024791083219623281733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3889349860722146415521155 5834024791083219623281733)
                  ·
                    refine ⟨1093879648328103679365325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5834024791083219623281733 1093879648328103679365325)
                    ·
                      rfl

theorem cell23_6390969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2, 2, 1, 4].length) (baseStart_6390969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6390969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6390969 prefixEnd_6390969 := by exact prefixLift 6390969
  have htrace : WordTrace (prefixWord ++ tailWord_6390969) baseStart_6390969 baseEnd_6390969 := by
    simpa [prefixWord, tailWord_6390969, baseEnd_6390969] using wordTrace_append hprefix tailTrace_6390969
  have hstable : (prefixWord ++ tailWord_6390969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6390969).length < 2 ^ (prefixWord ++ tailWord_6390969).sum := by decide
  have hdescent : baseEnd_6390969 < baseStart_6390969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6390969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6390996 : List Nat := [2, 4, 1, 4, 2, 1, 1, 1, 2, 2, 3]
def baseStart_6390996 : Nat := 118140960795 + 6390996 * 2 ^ 59
def prefixEnd_6390996 : Nat := 4983230072969 + 3 ^ 40 * 6390996 * 2
def baseEnd_6390996 : Nat := 3281652808961982432458351

theorem tailTrace_6390996 : CollatzResearch.WordTrace tailWord_6390996 prefixEnd_6390996 3281652808961982432458351 := by
  unfold tailWord_6390996
  simp only [CollatzResearch.WordTrace]
  refine ⟨116549386977260231031768421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155399182636346974709024561 116549386977260231031768421)
  ·
    refine ⟨21853010058236293318456579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116549386977260231031768421 21853010058236293318456579)
    ·
      refine ⟨32779515087354439977684869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21853010058236293318456579 32779515087354439977684869)
      ·
        refine ⟨6146159078878957495815913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32779515087354439977684869 6146159078878957495815913)
        ·
          refine ⟨4609619309159218121861935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6146159078878957495815913 4609619309159218121861935)
          ·
            refine ⟨6914428963738827182792903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4609619309159218121861935 6914428963738827182792903)
            ·
              refine ⟨10371643445608240774189355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6914428963738827182792903 10371643445608240774189355)
              ·
                refine ⟨15557465168412361161284033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10371643445608240774189355 15557465168412361161284033)
                ·
                  refine ⟨11668098876309270870963025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15557465168412361161284033 11668098876309270870963025)
                  ·
                    refine ⟨8751074157231953153222269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11668098876309270870963025 8751074157231953153222269)
                    ·
                      refine ⟨3281652808961982432458351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8751074157231953153222269 3281652808961982432458351)
                      ·
                        rfl

theorem cell23_6390996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_6390996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6390996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6390996 prefixEnd_6390996 := by exact prefixLift 6390996
  have htrace : WordTrace (prefixWord ++ tailWord_6390996) baseStart_6390996 baseEnd_6390996 := by
    simpa [prefixWord, tailWord_6390996, baseEnd_6390996] using wordTrace_append hprefix tailTrace_6390996
  have hstable : (prefixWord ++ tailWord_6390996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6390996).length < 2 ^ (prefixWord ++ tailWord_6390996).sum := by decide
  have hdescent : baseEnd_6390996 < baseStart_6390996 := by decide
  rcases family_descends (prefixWord ++ tailWord_6390996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6391008 : List Nat := [2, 1, 1, 3, 1, 4, 2, 2, 1, 6]
def baseStart_6391008 : Nat := 118140960795 + 6391008 * 2 ^ 59
def prefixEnd_6391008 : Nat := 4983230072969 + 3 ^ 40 * 6391008 * 2
def baseEnd_6391008 : Nat := 1093886323576612128502765

theorem tailTrace_6391008 : CollatzResearch.WordTrace tailWord_6391008 prefixEnd_6391008 1093886323576612128502765 := by
  unfold tailWord_6391008
  simp only [CollatzResearch.WordTrace]
  refine ⟨116549605815238494056486839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155399474420317992075315785 116549605815238494056486839)
  ·
    refine ⟨174824408722857741084730259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116549605815238494056486839 174824408722857741084730259)
    ·
      refine ⟨262236613084286611627095389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174824408722857741084730259 262236613084286611627095389)
      ·
        refine ⟨98338729906607479360160771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 262236613084286611627095389 98338729906607479360160771)
        ·
          refine ⟨147508094859911219040241157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98338729906607479360160771 147508094859911219040241157)
          ·
            refine ⟨27657767786233353570045217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 147508094859911219040241157 27657767786233353570045217)
            ·
              refine ⟨20743325839675015177533913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27657767786233353570045217 20743325839675015177533913)
              ·
                refine ⟨15557494379756261383150435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20743325839675015177533913 15557494379756261383150435)
                ·
                  refine ⟨23336241569634392074725653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15557494379756261383150435 23336241569634392074725653)
                  ·
                    refine ⟨1093886323576612128502765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23336241569634392074725653 1093886323576612128502765)
                    ·
                      rfl

theorem cell23_6391008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 2, 1, 6].length) (baseStart_6391008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6391008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6391008 prefixEnd_6391008 := by exact prefixLift 6391008
  have htrace : WordTrace (prefixWord ++ tailWord_6391008) baseStart_6391008 baseEnd_6391008 := by
    simpa [prefixWord, tailWord_6391008, baseEnd_6391008] using wordTrace_append hprefix tailTrace_6391008
  have hstable : (prefixWord ++ tailWord_6391008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6391008).length < 2 ^ (prefixWord ++ tailWord_6391008).sum := by decide
  have hdescent : baseEnd_6391008 < baseStart_6391008 := by decide
  rcases family_descends (prefixWord ++ tailWord_6391008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6391009 : List Nat := [1, 2, 3, 1, 3, 3, 2, 3, 1, 1, 3]
def baseStart_6391009 : Nat := 118140960795 + 6391009 * 2 ^ 59
def prefixEnd_6391009 : Nat := 4983230072969 + 3 ^ 40 * 6391009 * 2
def baseEnd_6391009 : Nat := 3281659484210490881595791

theorem tailTrace_6391009 : CollatzResearch.WordTrace tailWord_6391009 prefixEnd_6391009 3281659484210490881595791 := by
  unfold tailWord_6391009
  simp only [CollatzResearch.WordTrace]
  refine ⟨233099248103473365283760081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155399498735648910189173387 233099248103473365283760081)
  ·
    refine ⟨174824436077605023962820061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233099248103473365283760081 174824436077605023962820061)
    ·
      refine ⟨65559163529101883986057523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174824436077605023962820061 65559163529101883986057523)
      ·
        refine ⟨98338745293652825979086285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65559163529101883986057523 98338745293652825979086285)
        ·
          refine ⟨36877029485119809742157357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98338745293652825979086285 36877029485119809742157357)
          ·
            refine ⟨13828886056919928653309009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36877029485119809742157357 13828886056919928653309009)
            ·
              refine ⟨10371664542689946489981757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13828886056919928653309009 10371664542689946489981757)
              ·
                refine ⟨3889374203508729933743159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10371664542689946489981757 3889374203508729933743159)
                ·
                  refine ⟨5834061305263094900614739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3889374203508729933743159 5834061305263094900614739)
                  ·
                    refine ⟨8751091957894642350922109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5834061305263094900614739 8751091957894642350922109)
                    ·
                      refine ⟨3281659484210490881595791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8751091957894642350922109 3281659484210490881595791)
                      ·
                        rfl

theorem cell23_6391009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 3, 1, 1, 3].length) (baseStart_6391009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6391009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6391009 prefixEnd_6391009 := by exact prefixLift 6391009
  have htrace : WordTrace (prefixWord ++ tailWord_6391009) baseStart_6391009 baseEnd_6391009 := by
    simpa [prefixWord, tailWord_6391009, baseEnd_6391009] using wordTrace_append hprefix tailTrace_6391009
  have hstable : (prefixWord ++ tailWord_6391009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6391009).length < 2 ^ (prefixWord ++ tailWord_6391009).sum := by decide
  have hdescent : baseEnd_6391009 < baseStart_6391009 := by decide
  rcases family_descends (prefixWord ++ tailWord_6391009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6391052 : List Nat := [2, 2, 1, 2, 2, 4, 2, 2, 1, 2, 3]
def baseStart_6391052 : Nat := 118140960795 + 6391052 * 2 ^ 59
def prefixEnd_6391052 : Nat := 4983230072969 + 3 ^ 40 * 6391052 * 2
def baseEnd_6391052 : Nat := 3281681563878634213358093

theorem tailTrace_6391052 : CollatzResearch.WordTrace tailWord_6391052 prefixEnd_6391052 3281681563878634213358093 := by
  unfold tailWord_6391052
  simp only [CollatzResearch.WordTrace]
  refine ⟨116550408221158791813787705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155400544294878389085050273 116550408221158791813787705)
  ·
    refine ⟨87412806165869093860340779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116550408221158791813787705 87412806165869093860340779)
    ·
      refine ⟨131119209248803640790511169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87412806165869093860340779 131119209248803640790511169)
      ·
        refine ⟨98339406936602730592883377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131119209248803640790511169 98339406936602730592883377)
        ·
          refine ⟨73754555202452047944662533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98339406936602730592883377 73754555202452047944662533)
          ·
            refine ⟨13828979100459758989624225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73754555202452047944662533 13828979100459758989624225)
            ·
              refine ⟨10371734325344819242218169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13828979100459758989624225 10371734325344819242218169)
              ·
                refine ⟨7778800744008614431663627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10371734325344819242218169 7778800744008614431663627)
                ·
                  refine ⟨11668201116012921647495441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7778800744008614431663627 11668201116012921647495441)
                  ·
                    refine ⟨8751150837009691235621581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11668201116012921647495441 8751150837009691235621581)
                    ·
                      refine ⟨3281681563878634213358093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8751150837009691235621581 3281681563878634213358093)
                      ·
                        rfl

theorem cell23_6391052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 2, 1, 2, 3].length) (baseStart_6391052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6391052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6391052 prefixEnd_6391052 := by exact prefixLift 6391052
  have htrace : WordTrace (prefixWord ++ tailWord_6391052) baseStart_6391052 baseEnd_6391052 := by
    simpa [prefixWord, tailWord_6391052, baseEnd_6391052] using wordTrace_append hprefix tailTrace_6391052
  have hstable : (prefixWord ++ tailWord_6391052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6391052).length < 2 ^ (prefixWord ++ tailWord_6391052).sum := by decide
  have hdescent : baseEnd_6391052 < baseStart_6391052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6391052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6391066 : List Nat := [3, 1, 1, 3, 3, 1, 3, 3, 1, 2, 2]
def baseStart_6391066 : Nat := 118140960795 + 6391066 * 2 ^ 59
def prefixEnd_6391066 : Nat := 4983230072969 + 3 ^ 40 * 6391066 * 2
def baseEnd_6391066 : Nat := 3281688752607797158583029

theorem tailTrace_6391066 : CollatzResearch.WordTrace tailWord_6391066 prefixEnd_6391066 3281688752607797158583029 := by
  unfold tailWord_6391066
  simp only [CollatzResearch.WordTrace]
  refine ⟨58275331766066716004646263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155400884709511242679056701 58275331766066716004646263)
  ·
    refine ⟨87412997649100074006969395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58275331766066716004646263 87412997649100074006969395)
    ·
      refine ⟨131119496473650111010454093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87412997649100074006969395 131119496473650111010454093)
      ·
        refine ⟨49169811177618791628920285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131119496473650111010454093 49169811177618791628920285)
        ·
          refine ⟨18438679191607046860845107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49169811177618791628920285 18438679191607046860845107)
          ·
            refine ⟨27658018787410570291267661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18438679191607046860845107 27658018787410570291267661)
            ·
              refine ⟨10371757045278963859225373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27658018787410570291267661 10371757045278963859225373)
              ·
                refine ⟨3889408891979611447209515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10371757045278963859225373 3889408891979611447209515)
                ·
                  refine ⟨5834113337969417170814273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3889408891979611447209515 5834113337969417170814273)
                  ·
                    refine ⟨4375585003477062878110705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5834113337969417170814273 4375585003477062878110705)
                    ·
                      refine ⟨3281688752607797158583029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4375585003477062878110705 3281688752607797158583029)
                      ·
                        rfl

theorem cell23_6391066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 3, 1, 2, 2].length) (baseStart_6391066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6391066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6391066 prefixEnd_6391066 := by exact prefixLift 6391066
  have htrace : WordTrace (prefixWord ++ tailWord_6391066) baseStart_6391066 baseEnd_6391066 := by
    simpa [prefixWord, tailWord_6391066, baseEnd_6391066] using wordTrace_append hprefix tailTrace_6391066
  have hstable : (prefixWord ++ tailWord_6391066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6391066).length < 2 ^ (prefixWord ++ tailWord_6391066).sum := by decide
  have hdescent : baseEnd_6391066 < baseStart_6391066 := by decide
  rcases family_descends (prefixWord ++ tailWord_6391066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6391088 : List Nat := [2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 4]
def baseStart_6391088 : Nat := 118140960795 + 6391088 * 2 ^ 59
def prefixEnd_6391088 : Nat := 4983230072969 + 3 ^ 40 * 6391088 * 2
def baseEnd_6391088 : Nat := 3281700049182196072507927

theorem tailTrace_6391088 : CollatzResearch.WordTrace tailWord_6391088 prefixEnd_6391088 3281700049182196072507927 := by
  unfold tailWord_6391088
  simp only [CollatzResearch.WordTrace]
  refine ⟨116551064735093580887942959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155401419646791441183923945 116551064735093580887942959)
  ·
    refine ⟨174826597102640371331914439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116551064735093580887942959 174826597102640371331914439)
    ·
      refine ⟨262239895653960556997871659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174826597102640371331914439 262239895653960556997871659)
      ·
        refine ⟨393359843480940835496807489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262239895653960556997871659 393359843480940835496807489)
        ·
          refine ⟨295019882610705626622605617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 393359843480940835496807489 295019882610705626622605617)
          ·
            refine ⟨221264911958029219966954213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295019882610705626622605617 221264911958029219966954213)
            ·
              refine ⟨41487170992130478743803915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 221264911958029219966954213 41487170992130478743803915)
              ·
                refine ⟨62230756488195718115705873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41487170992130478743803915 62230756488195718115705873)
                ·
                  refine ⟨46673067366146788586779405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62230756488195718115705873 46673067366146788586779405)
                  ·
                    refine ⟨17502400262305045720042277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46673067366146788586779405 17502400262305045720042277)
                    ·
                      refine ⟨3281700049182196072507927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17502400262305045720042277 3281700049182196072507927)
                      ·
                        rfl

theorem cell23_6391088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 4].length) (baseStart_6391088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6391088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6391088 prefixEnd_6391088 := by exact prefixLift 6391088
  have htrace : WordTrace (prefixWord ++ tailWord_6391088) baseStart_6391088 baseEnd_6391088 := by
    simpa [prefixWord, tailWord_6391088, baseEnd_6391088] using wordTrace_append hprefix tailTrace_6391088
  have hstable : (prefixWord ++ tailWord_6391088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6391088).length < 2 ^ (prefixWord ++ tailWord_6391088).sum := by decide
  have hdescent : baseEnd_6391088 < baseStart_6391088 := by decide
  rcases family_descends (prefixWord ++ tailWord_6391088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6391098 : List Nat := [3, 1, 1, 1, 4, 1, 2, 1, 1, 8]
def baseStart_6391098 : Nat := 118140960795 + 6391098 * 2 ^ 59
def prefixEnd_6391098 : Nat := 4983230072969 + 3 ^ 40 * 6391098 * 2
def baseEnd_6391098 : Nat := 1093901727996247011127627

theorem tailTrace_6391098 : CollatzResearch.WordTrace tailWord_6391098 prefixEnd_6391098 1093901727996247011127627 := by
  unfold tailWord_6391098
  simp only [CollatzResearch.WordTrace]
  refine ⟨58275623550037733370937487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155401662800100622322499965 58275623550037733370937487)
  ·
    refine ⟨87413435325056600056406231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58275623550037733370937487 87413435325056600056406231)
    ·
      refine ⟨131120152987584900084609347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87413435325056600056406231 131120152987584900084609347)
      ·
        refine ⟨196680229481377350126914021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131120152987584900084609347 196680229481377350126914021)
        ·
          refine ⟨36877543027758253148796379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 196680229481377350126914021 36877543027758253148796379)
          ·
            refine ⟨55316314541637379723194569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36877543027758253148796379 55316314541637379723194569)
            ·
              refine ⟨41487235906228034792395927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55316314541637379723194569 41487235906228034792395927)
              ·
                refine ⟨62230853859342052188593891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41487235906228034792395927 62230853859342052188593891)
                ·
                  refine ⟨93346280789013078282890837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62230853859342052188593891 93346280789013078282890837)
                  ·
                    refine ⟨1093901727996247011127627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 93346280789013078282890837 1093901727996247011127627)
                    ·
                      rfl

theorem cell23_6391098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 1, 8].length) (baseStart_6391098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6391098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6391098 prefixEnd_6391098 := by exact prefixLift 6391098
  have htrace : WordTrace (prefixWord ++ tailWord_6391098) baseStart_6391098 baseEnd_6391098 := by
    simpa [prefixWord, tailWord_6391098, baseEnd_6391098] using wordTrace_append hprefix tailTrace_6391098
  have hstable : (prefixWord ++ tailWord_6391098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6391098).length < 2 ^ (prefixWord ++ tailWord_6391098).sum := by decide
  have hdescent : baseEnd_6391098 < baseStart_6391098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6391098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6391125 : List Nat := [1, 3, 2, 2, 3, 1, 2, 1, 2, 1, 5]
def baseStart_6391125 : Nat := 118140960795 + 6391125 * 2 ^ 59
def prefixEnd_6391125 : Nat := 4983230072969 + 3 ^ 40 * 6391125 * 2
def baseEnd_6391125 : Nat := 3281719047966412427745257

theorem tailTrace_6391125 : CollatzResearch.WordTrace tailWord_6391125 prefixEnd_6391125 3281719047966412427745257 := by
  unfold tailWord_6391125
  simp only [CollatzResearch.WordTrace]
  refine ⟨233103478971053117094982829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155402319314035411396655219 233103478971053117094982829)
  ·
    refine ⟨87413804614144918910618561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233103478971053117094982829 87413804614144918910618561)
    ·
      refine ⟨65560353460608689182963921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87413804614144918910618561 65560353460608689182963921)
      ·
        refine ⟨49170265095456516887222941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65560353460608689182963921 49170265095456516887222941)
        ·
          refine ⟨18438849410796193832708603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49170265095456516887222941 18438849410796193832708603)
          ·
            refine ⟨27658274116194290749062905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18438849410796193832708603 27658274116194290749062905)
            ·
              refine ⟨20743705587145718061797179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27658274116194290749062905 20743705587145718061797179)
              ·
                refine ⟨31115558380718577092695769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20743705587145718061797179 31115558380718577092695769)
                ·
                  refine ⟨23336668785538932819521827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31115558380718577092695769 23336668785538932819521827)
                  ·
                    refine ⟨35005003178308399229282741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23336668785538932819521827 35005003178308399229282741)
                    ·
                      refine ⟨3281719047966412427745257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35005003178308399229282741 3281719047966412427745257)
                      ·
                        rfl

theorem cell23_6391125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_6391125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6391125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6391125 prefixEnd_6391125 := by exact prefixLift 6391125
  have htrace : WordTrace (prefixWord ++ tailWord_6391125) baseStart_6391125 baseEnd_6391125 := by
    simpa [prefixWord, tailWord_6391125, baseEnd_6391125] using wordTrace_append hprefix tailTrace_6391125
  have hstable : (prefixWord ++ tailWord_6391125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6391125).length < 2 ^ (prefixWord ++ tailWord_6391125).sum := by decide
  have hdescent : baseEnd_6391125 < baseStart_6391125 := by decide
  rcases family_descends (prefixWord ++ tailWord_6391125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6391139 : List Nat := [1, 1, 1, 5, 2, 2, 1, 4, 2, 2, 2]
def baseStart_6391139 : Nat := 118140960795 + 6391139 * 2 ^ 59
def prefixEnd_6391139 : Nat := 4983230072969 + 3 ^ 40 * 6391139 * 2
def baseEnd_6391139 : Nat := 3281726236695575372970193

theorem tailTrace_6391139 : CollatzResearch.WordTrace tailWord_6391139 prefixEnd_6391139 3281726236695575372970193 := by
  unfold tailWord_6391139
  simp only [CollatzResearch.WordTrace]
  refine ⟨233103989593002397485992471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155402659728668264990661647 233103989593002397485992471)
  ·
    refine ⟨349655984389503596228988707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233103989593002397485992471 349655984389503596228988707)
    ·
      refine ⟨524483976584255394343483061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349655984389503596228988707 524483976584255394343483061)
      ·
        refine ⟨49170372804773943219701537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 524483976584255394343483061 49170372804773943219701537)
        ·
          refine ⟨36877779603580457414776153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49170372804773943219701537 36877779603580457414776153)
          ·
            refine ⟨27658334702685343061082115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36877779603580457414776153 27658334702685343061082115)
            ·
              refine ⟨41487502054028014591623173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27658334702685343061082115 41487502054028014591623173)
              ·
                refine ⟨7778906635130252735929345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41487502054028014591623173 7778906635130252735929345)
                ·
                  refine ⟨5834179976347689551947009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7778906635130252735929345 5834179976347689551947009)
                  ·
                    refine ⟨4375634982260767163960257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5834179976347689551947009 4375634982260767163960257)
                    ·
                      refine ⟨3281726236695575372970193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4375634982260767163960257 3281726236695575372970193)
                      ·
                        rfl

theorem cell23_6391139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 4, 2, 2, 2].length) (baseStart_6391139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6391139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6391139 prefixEnd_6391139 := by exact prefixLift 6391139
  have htrace : WordTrace (prefixWord ++ tailWord_6391139) baseStart_6391139 baseEnd_6391139 := by
    simpa [prefixWord, tailWord_6391139, baseEnd_6391139] using wordTrace_append hprefix tailTrace_6391139
  have hstable : (prefixWord ++ tailWord_6391139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6391139).length < 2 ^ (prefixWord ++ tailWord_6391139).sum := by decide
  have hdescent : baseEnd_6391139 < baseStart_6391139 := by decide
  rcases family_descends (prefixWord ++ tailWord_6391139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6391168 : List Nat := [2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 7]
def baseStart_6391168 : Nat := 118140960795 + 6391168 * 2 ^ 59
def prefixEnd_6391168 : Nat := 4983230072969 + 3 ^ 40 * 6391168 * 2
def baseEnd_6391168 : Nat := 3281741127634555759507559

theorem tailTrace_6391168 : CollatzResearch.WordTrace tailWord_6391168 prefixEnd_6391168 3281741127634555759507559 := by
  unfold tailWord_6391168
  simp only [CollatzResearch.WordTrace]
  refine ⟨116552523654948667719399079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155403364873264890292532105 116552523654948667719399079)
  ·
    refine ⟨174828785482423001579098619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116552523654948667719399079 174828785482423001579098619)
    ·
      refine ⟨262243178223634502368647929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174828785482423001579098619 262243178223634502368647929)
      ·
        refine ⟨196682383667725876776485947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262243178223634502368647929 196682383667725876776485947)
        ·
          refine ⟨295023575501588815164728921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196682383667725876776485947 295023575501588815164728921)
          ·
            refine ⟨221267681626191611373546691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295023575501588815164728921 221267681626191611373546691)
            ·
              refine ⟨331901522439287417060320037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221267681626191611373546691 331901522439287417060320037)
              ·
                refine ⟨62231535457366390698810007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 331901522439287417060320037 62231535457366390698810007)
                ·
                  refine ⟨93347303186049586048215011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62231535457366390698810007 93347303186049586048215011)
                  ·
                    refine ⟨140020954779074379072322517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 93347303186049586048215011 140020954779074379072322517)
                    ·
                      refine ⟨3281741127634555759507559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 140020954779074379072322517 3281741127634555759507559)
                      ·
                        rfl

theorem cell23_6391168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 7].length) (baseStart_6391168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6391168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6391168 prefixEnd_6391168 := by exact prefixLift 6391168
  have htrace : WordTrace (prefixWord ++ tailWord_6391168) baseStart_6391168 baseEnd_6391168 := by
    simpa [prefixWord, tailWord_6391168, baseEnd_6391168] using wordTrace_append hprefix tailTrace_6391168
  have hstable : (prefixWord ++ tailWord_6391168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6391168).length < 2 ^ (prefixWord ++ tailWord_6391168).sum := by decide
  have hdescent : baseEnd_6391168 < baseStart_6391168 := by decide
  rcases family_descends (prefixWord ++ tailWord_6391168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6391175 : List Nat := [1, 1, 4, 2, 2, 3, 1, 1, 1, 7]
def baseStart_6391175 : Nat := 118140960795 + 6391175 * 2 ^ 59
def prefixEnd_6391175 : Nat := 4983230072969 + 3 ^ 40 * 6391175 * 2
def baseEnd_6391175 : Nat := 1093914907333045744040009

theorem tailTrace_6391175 : CollatzResearch.WordTrace tailWord_6391175 prefixEnd_6391175 1093914907333045744040009 := by
  unfold tailWord_6391175
  simp only [CollatzResearch.WordTrace]
  refine ⟨233105302620871975634302979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155403535080581317089535319 233105302620871975634302979)
  ·
    refine ⟨349657953931307963451454469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233105302620871975634302979 349657953931307963451454469)
    ·
      refine ⟨65560866362120243147147713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 349657953931307963451454469 65560866362120243147147713)
      ·
        refine ⟨49170649771590182360360785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65560866362120243147147713 49170649771590182360360785)
        ·
          refine ⟨36877987328692636770270589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49170649771590182360360785 36877987328692636770270589)
          ·
            refine ⟨13829245248259738788851471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36877987328692636770270589 13829245248259738788851471)
            ·
              refine ⟨20743867872389608183277207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13829245248259738788851471 20743867872389608183277207)
              ·
                refine ⟨31115801808584412274915811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20743867872389608183277207 31115801808584412274915811)
                ·
                  refine ⟨46673702712876618412373717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31115801808584412274915811 46673702712876618412373717)
                  ·
                    refine ⟨1093914907333045744040009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46673702712876618412373717 1093914907333045744040009)
                    ·
                      rfl

theorem cell23_6391175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 7].length) (baseStart_6391175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6391175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6391175 prefixEnd_6391175 := by exact prefixLift 6391175
  have htrace : WordTrace (prefixWord ++ tailWord_6391175) baseStart_6391175 baseEnd_6391175 := by
    simpa [prefixWord, tailWord_6391175, baseEnd_6391175] using wordTrace_append hprefix tailTrace_6391175
  have hstable : (prefixWord ++ tailWord_6391175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6391175).length < 2 ^ (prefixWord ++ tailWord_6391175).sum := by decide
  have hdescent : baseEnd_6391175 < baseStart_6391175 := by decide
  rcases family_descends (prefixWord ++ tailWord_6391175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6391212 : List Nat := [2, 2, 1, 1, 1, 1, 6, 1, 2, 4, 2]
def baseStart_6391212 : Nat := 118140960795 + 6391212 * 2 ^ 59
def prefixEnd_6391212 : Nat := 4983230072969 + 3 ^ 40 * 6391212 * 2
def baseEnd_6391212 : Nat := 3281763720783353587357357

theorem tailTrace_6391212 : CollatzResearch.WordTrace tailWord_6391212 prefixEnd_6391212 3281763720783353587357357 := by
  unfold tailWord_6391212
  simp only [CollatzResearch.WordTrace]
  refine ⟨116553326060868965476699945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155404434747825287302266593 116553326060868965476699945)
  ·
    refine ⟨87414994545651724107524959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116553326060868965476699945 87414994545651724107524959)
    ·
      refine ⟨131122491818477586161287439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87414994545651724107524959 131122491818477586161287439)
      ·
        refine ⟨196683737727716379241931159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131122491818477586161287439 196683737727716379241931159)
        ·
          refine ⟨295025606591574568862896739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196683737727716379241931159 295025606591574568862896739)
          ·
            refine ⟨442538409887361853294345109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295025606591574568862896739 442538409887361853294345109)
            ·
              refine ⟨20743987963470086873172427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 442538409887361853294345109 20743987963470086873172427)
              ·
                refine ⟨31115981945205130309758641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20743987963470086873172427 31115981945205130309758641)
                ·
                  refine ⟨23336986458903847732318981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31115981945205130309758641 23336986458903847732318981)
                  ·
                    refine ⟨4375684961044471449809809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23336986458903847732318981 4375684961044471449809809)
                    ·
                      refine ⟨3281763720783353587357357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4375684961044471449809809 3281763720783353587357357)
                      ·
                        rfl

theorem cell23_6391212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 4, 2].length) (baseStart_6391212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6391212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6391212 prefixEnd_6391212 := by exact prefixLift 6391212
  have htrace : WordTrace (prefixWord ++ tailWord_6391212) baseStart_6391212 baseEnd_6391212 := by
    simpa [prefixWord, tailWord_6391212, baseEnd_6391212] using wordTrace_append hprefix tailTrace_6391212
  have hstable : (prefixWord ++ tailWord_6391212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6391212).length < 2 ^ (prefixWord ++ tailWord_6391212).sum := by decide
  have hdescent : baseEnd_6391212 < baseStart_6391212 := by decide
  rcases family_descends (prefixWord ++ tailWord_6391212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6391269 : List Nat := [1, 3, 1, 5, 1, 1, 4, 1, 6]
def baseStart_6391269 : Nat := 118140960795 + 6391269 * 2 ^ 59
def prefixEnd_6391269 : Nat := 4983230072969 + 3 ^ 40 * 6391269 * 2
def baseEnd_6391269 : Nat := 364643665464517762704955

theorem tailTrace_6391269 : CollatzResearch.WordTrace tailWord_6391269 prefixEnd_6391269 364643665464517762704955 := by
  unfold tailWord_6391269
  simp only [CollatzResearch.WordTrace]
  refine ⟨233108731082531429688224861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155405820721687619792149907 233108731082531429688224861)
  ·
    refine ⟨87415774155949286133084323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233108731082531429688224861 87415774155949286133084323)
    ·
      refine ⟨131123661233923929199626485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87415774155949286133084323 131123661233923929199626485)
      ·
        refine ⟨12292843240680368362464983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 131123661233923929199626485 12292843240680368362464983)
        ·
          refine ⟨18439264861020552543697475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12292843240680368362464983 18439264861020552543697475)
          ·
            refine ⟨27658897291530828815546213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18439264861020552543697475 27658897291530828815546213)
            ·
              refine ⟨5186043242162030402914915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27658897291530828815546213 5186043242162030402914915)
              ·
                refine ⟨7779064863243045604372373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5186043242162030402914915 7779064863243045604372373)
                ·
                  refine ⟨364643665464517762704955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7779064863243045604372373 364643665464517762704955)
                  ·
                    rfl

theorem cell23_6391269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4, 1, 6].length) (baseStart_6391269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6391269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6391269 prefixEnd_6391269 := by exact prefixLift 6391269
  have htrace : WordTrace (prefixWord ++ tailWord_6391269) baseStart_6391269 baseEnd_6391269 := by
    simpa [prefixWord, tailWord_6391269, baseEnd_6391269] using wordTrace_append hprefix tailTrace_6391269
  have hstable : (prefixWord ++ tailWord_6391269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6391269).length < 2 ^ (prefixWord ++ tailWord_6391269).sum := by decide
  have hdescent : baseEnd_6391269 < baseStart_6391269 := by decide
  rcases family_descends (prefixWord ++ tailWord_6391269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6391329 : List Nat := [1, 2, 3, 2, 2, 2, 2, 3, 2, 4]
def baseStart_6391329 : Nat := 118140960795 + 6391329 * 2 ^ 59
def prefixEnd_6391329 : Nat := 4983230072969 + 3 ^ 40 * 6391329 * 2
def baseEnd_6391329 : Nat := 1093941266006643209864773

theorem tailTrace_6391329 : CollatzResearch.WordTrace tailWord_6391329 prefixEnd_6391329 1093941266006643209864773 := by
  unfold tailWord_6391329
  simp only [CollatzResearch.WordTrace]
  refine ⟨233110919462314059935409041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155407279641542706623606027 233110919462314059935409041)
  ·
    refine ⟨174833189596735544951556781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233110919462314059935409041 174833189596735544951556781)
    ·
      refine ⟨65562446098775829356833793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174833189596735544951556781 65562446098775829356833793)
      ·
        refine ⟨49171834574081872017625345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65562446098775829356833793 49171834574081872017625345)
        ·
          refine ⟨36878875930561404013219009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49171834574081872017625345 36878875930561404013219009)
          ·
            refine ⟨27659156947921053009914257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36878875930561404013219009 27659156947921053009914257)
            ·
              refine ⟨20744367710940789757435693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27659156947921053009914257 20744367710940789757435693)
              ·
                refine ⟨7779137891602796159038385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20744367710940789757435693 7779137891602796159038385)
                ·
                  refine ⟨5834353418702097119278789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7779137891602796159038385 5834353418702097119278789)
                  ·
                    refine ⟨1093941266006643209864773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5834353418702097119278789 1093941266006643209864773)
                    ·
                      rfl

theorem cell23_6391329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 3, 2, 4].length) (baseStart_6391329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6391329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6391329 prefixEnd_6391329 := by exact prefixLift 6391329
  have htrace : WordTrace (prefixWord ++ tailWord_6391329) baseStart_6391329 baseEnd_6391329 := by
    simpa [prefixWord, tailWord_6391329, baseEnd_6391329] using wordTrace_append hprefix tailTrace_6391329
  have hstable : (prefixWord ++ tailWord_6391329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6391329).length < 2 ^ (prefixWord ++ tailWord_6391329).sum := by decide
  have hdescent : baseEnd_6391329 < baseStart_6391329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6391329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6391350 : List Nat := [5, 1, 2, 1, 4, 1, 2, 1, 1, 5]
def baseStart_6391350 : Nat := 118140960795 + 6391350 * 2 ^ 59
def prefixEnd_6391350 : Nat := 4983230072969 + 3 ^ 40 * 6391350 * 2
def baseEnd_6391350 : Nat := 1093944860371224682477241

theorem tailTrace_6391350 : CollatzResearch.WordTrace tailWord_6391350 prefixEnd_6391350 1093944860371224682477241 := by
  unfold tailWord_6391350
  simp only [CollatzResearch.WordTrace]
  refine ⟨14569480337202373782620219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 155407790263491987014615669 14569480337202373782620219)
  ·
    refine ⟨21854220505803560673930329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14569480337202373782620219 21854220505803560673930329)
    ·
      refine ⟨16390665379352670505447747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21854220505803560673930329 16390665379352670505447747)
      ·
        refine ⟨24585998069029005758171621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16390665379352670505447747 24585998069029005758171621)
        ·
          refine ⟨4609874637942938579657179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24585998069029005758171621 4609874637942938579657179)
          ·
            refine ⟨6914811956914407869485769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4609874637942938579657179 6914811956914407869485769)
            ·
              refine ⟨5186108967685805902114327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6914811956914407869485769 5186108967685805902114327)
              ·
                refine ⟨7779163451528708853171491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5186108967685805902114327 7779163451528708853171491)
                ·
                  refine ⟨11668745177293063279757237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7779163451528708853171491 11668745177293063279757237)
                  ·
                    refine ⟨1093944860371224682477241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11668745177293063279757237 1093944860371224682477241)
                    ·
                      rfl

theorem cell23_6391350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_6391350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6391350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6391350 prefixEnd_6391350 := by exact prefixLift 6391350
  have htrace : WordTrace (prefixWord ++ tailWord_6391350) baseStart_6391350 baseEnd_6391350 := by
    simpa [prefixWord, tailWord_6391350, baseEnd_6391350] using wordTrace_append hprefix tailTrace_6391350
  have hstable : (prefixWord ++ tailWord_6391350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6391350).length < 2 ^ (prefixWord ++ tailWord_6391350).sum := by decide
  have hdescent : baseEnd_6391350 < baseStart_6391350 := by decide
  rcases family_descends (prefixWord ++ tailWord_6391350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6391353 : List Nat := [1, 2, 1, 5, 1, 2, 1, 5, 1, 2, 2]
def baseStart_6391353 : Nat := 118140960795 + 6391353 * 2 ^ 59
def prefixEnd_6391353 : Nat := 4983230072969 + 3 ^ 40 * 6391353 * 2
def baseEnd_6391353 : Nat := 3281836121555637535694209

theorem tailTrace_6391353 : CollatzResearch.WordTrace tailWord_6391353 prefixEnd_6391353 3281836121555637535694209 := by
  unfold tailWord_6391353
  simp only [CollatzResearch.WordTrace]
  refine ⟨233111794814227112034282713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155407863209484741356188475 233111794814227112034282713)
  ·
    refine ⟨174833846110670334025712035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233111794814227112034282713 174833846110670334025712035)
    ·
      refine ⟨262250769166005501038568053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174833846110670334025712035 262250769166005501038568053)
      ·
        refine ⟨24586009609313015722365755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 262250769166005501038568053 24586009609313015722365755)
        ·
          refine ⟨36879014413969523583548633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24586009609313015722365755 36879014413969523583548633)
          ·
            refine ⟨27659260810477142687661475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36879014413969523583548633 27659260810477142687661475)
            ·
              refine ⟨41488891215715714031492213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27659260810477142687661475 41488891215715714031492213)
              ·
                refine ⟨3889583551473348190452395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41488891215715714031492213 3889583551473348190452395)
                ·
                  refine ⟨5834375327210022285678593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3889583551473348190452395 5834375327210022285678593)
                  ·
                    refine ⟨4375781495407516714258945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5834375327210022285678593 4375781495407516714258945)
                    ·
                      refine ⟨3281836121555637535694209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4375781495407516714258945 3281836121555637535694209)
                      ·
                        rfl

theorem cell23_6391353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_6391353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6391353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6391353 prefixEnd_6391353 := by exact prefixLift 6391353
  have htrace : WordTrace (prefixWord ++ tailWord_6391353) baseStart_6391353 baseEnd_6391353 := by
    simpa [prefixWord, tailWord_6391353, baseEnd_6391353] using wordTrace_append hprefix tailTrace_6391353
  have hstable : (prefixWord ++ tailWord_6391353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6391353).length < 2 ^ (prefixWord ++ tailWord_6391353).sum := by decide
  have hdescent : baseEnd_6391353 < baseStart_6391353 := by decide
  rcases family_descends (prefixWord ++ tailWord_6391353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6391356 : List Nat := [2, 2, 2, 2, 4, 1, 1, 3, 1, 2, 3]
def baseStart_6391356 : Nat := 118140960795 + 6391356 * 2 ^ 59
def prefixEnd_6391356 : Nat := 4983230072969 + 3 ^ 40 * 6391356 * 2
def baseEnd_6391356 : Nat := 3281837661997601023956695

theorem tailTrace_6391356 : CollatzResearch.WordTrace tailWord_6391356 prefixEnd_6391356 3281837661997601023956695 := by
  unfold tailWord_6391356
  simp only [CollatzResearch.WordTrace]
  refine ⟨116555952116608121773320961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155407936155477495697761281 116555952116608121773320961)
  ·
    refine ⟨87416964087456091329990721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116555952116608121773320961 87416964087456091329990721)
    ·
      refine ⟨65562723065592068497493041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87416964087456091329990721 65562723065592068497493041)
      ·
        refine ⟨49172042299194051373119781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65562723065592068497493041 49172042299194051373119781)
        ·
          refine ⟨9219757931098884632459959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49172042299194051373119781 9219757931098884632459959)
          ·
            refine ⟨13829636896648326948689939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9219757931098884632459959 13829636896648326948689939)
            ·
              refine ⟨20744455344972490423034909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13829636896648326948689939 20744455344972490423034909)
              ·
                refine ⟨7779170754364683908638091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20744455344972490423034909 7779170754364683908638091)
                ·
                  refine ⟨11668756131547025862957137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7779170754364683908638091 11668756131547025862957137)
                  ·
                    refine ⟨8751567098660269397217853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11668756131547025862957137 8751567098660269397217853)
                    ·
                      refine ⟨3281837661997601023956695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8751567098660269397217853 3281837661997601023956695)
                      ·
                        rfl

theorem cell23_6391356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 3, 1, 2, 3].length) (baseStart_6391356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6391356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6391356 prefixEnd_6391356 := by exact prefixLift 6391356
  have htrace : WordTrace (prefixWord ++ tailWord_6391356) baseStart_6391356 baseEnd_6391356 := by
    simpa [prefixWord, tailWord_6391356, baseEnd_6391356] using wordTrace_append hprefix tailTrace_6391356
  have hstable : (prefixWord ++ tailWord_6391356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6391356).length < 2 ^ (prefixWord ++ tailWord_6391356).sum := by decide
  have hdescent : baseEnd_6391356 < baseStart_6391356 := by decide
  rcases family_descends (prefixWord ++ tailWord_6391356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6391396 : List Nat := [2, 3, 1, 1, 2, 3, 1, 4, 1, 3, 2]
def baseStart_6391396 : Nat := 118140960795 + 6391396 * 2 ^ 59
def prefixEnd_6391396 : Nat := 4983230072969 + 3 ^ 40 * 6391396 * 2
def baseEnd_6391396 : Nat := 3281858201223780867456511

theorem tailTrace_6391396 : CollatzResearch.WordTrace tailWord_6391396 prefixEnd_6391396 3281858201223780867456511 := by
  unfold tailWord_6391396
  simp only [CollatzResearch.WordTrace]
  refine ⟨116556681576535665189049021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155408908768714220252065361 116556681576535665189049021)
  ·
    refine ⟨43708755591200874445893383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116556681576535665189049021 43708755591200874445893383)
    ·
      refine ⟨65563133386801311668840075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43708755591200874445893383 65563133386801311668840075)
      ·
        refine ⟨98344700080201967503260113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65563133386801311668840075 98344700080201967503260113)
        ·
          refine ⟨73758525060151475627445085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98344700080201967503260113 73758525060151475627445085)
          ·
            refine ⟨27659446897556803360291907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73758525060151475627445085 27659446897556803360291907)
            ·
              refine ⟨41489170346335205040437861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27659446897556803360291907 41489170346335205040437861)
              ·
                refine ⟨7779219439937850945082099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41489170346335205040437861 7779219439937850945082099)
                ·
                  refine ⟨11668829159906776417623149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7779219439937850945082099 11668829159906776417623149)
                  ·
                    refine ⟨4375810934965041156608681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11668829159906776417623149 4375810934965041156608681)
                    ·
                      refine ⟨3281858201223780867456511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4375810934965041156608681 3281858201223780867456511)
                      ·
                        rfl

theorem cell23_6391396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 4, 1, 3, 2].length) (baseStart_6391396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6391396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6391396 prefixEnd_6391396 := by exact prefixLift 6391396
  have htrace : WordTrace (prefixWord ++ tailWord_6391396) baseStart_6391396 baseEnd_6391396 := by
    simpa [prefixWord, tailWord_6391396, baseEnd_6391396] using wordTrace_append hprefix tailTrace_6391396
  have hstable : (prefixWord ++ tailWord_6391396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6391396).length < 2 ^ (prefixWord ++ tailWord_6391396).sum := by decide
  have hdescent : baseEnd_6391396 < baseStart_6391396 := by decide
  rcases family_descends (prefixWord ++ tailWord_6391396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6391409 : List Nat := [1, 2, 2, 2, 1, 1, 1, 6, 1, 4, 2]
def baseStart_6391409 : Nat := 118140960795 + 6391409 * 2 ^ 59
def prefixEnd_6391409 : Nat := 4983230072969 + 3 ^ 40 * 6391409 * 2
def baseEnd_6391409 : Nat := 3281864876472289316593951

theorem tailTrace_6391409 : CollatzResearch.WordTrace tailWord_6391409 prefixEnd_6391409 3281864876472289316593951 := by
  unfold tailWord_6391409
  simp only [CollatzResearch.WordTrace]
  refine ⟨233113837302024233598321281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155409224868016155732214187 233113837302024233598321281)
  ·
    refine ⟨174835377976518175198740961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233113837302024233598321281 174835377976518175198740961)
    ·
      refine ⟨131126533482388631399055721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174835377976518175198740961 131126533482388631399055721)
      ·
        refine ⟨98344900111791473549291791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131126533482388631399055721 98344900111791473549291791)
        ·
          refine ⟨147517350167687210323937687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98344900111791473549291791 147517350167687210323937687)
          ·
            refine ⟨221276025251530815485906531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147517350167687210323937687 221276025251530815485906531)
            ·
              refine ⟨331914037877296223228859797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221276025251530815485906531 331914037877296223228859797)
              ·
                refine ⟨15558470525498260463852803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 331914037877296223228859797 15558470525498260463852803)
                ·
                  refine ⟨23337705788247390695779205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15558470525498260463852803 23337705788247390695779205)
                  ·
                    refine ⟨4375819835296385755458601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23337705788247390695779205 4375819835296385755458601)
                    ·
                      refine ⟨3281864876472289316593951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4375819835296385755458601 3281864876472289316593951)
                      ·
                        rfl

theorem cell23_6391409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6, 1, 4, 2].length) (baseStart_6391409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6391409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6391409 prefixEnd_6391409 := by exact prefixLift 6391409
  have htrace : WordTrace (prefixWord ++ tailWord_6391409) baseStart_6391409 baseEnd_6391409 := by
    simpa [prefixWord, tailWord_6391409, baseEnd_6391409] using wordTrace_append hprefix tailTrace_6391409
  have hstable : (prefixWord ++ tailWord_6391409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6391409).length < 2 ^ (prefixWord ++ tailWord_6391409).sum := by decide
  have hdescent : baseEnd_6391409 < baseStart_6391409 := by decide
  rcases family_descends (prefixWord ++ tailWord_6391409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6391413 : List Nat := [1, 3, 4, 2, 1, 1, 2, 3, 1, 3, 2]
def baseStart_6391413 : Nat := 118140960795 + 6391413 * 2 ^ 59
def prefixEnd_6391413 : Nat := 4983230072969 + 3 ^ 40 * 6391413 * 2
def baseEnd_6391413 : Nat := 3281866930394907300943933

theorem tailTrace_6391413 : CollatzResearch.WordTrace tailWord_6391413 prefixEnd_6391413 3281866930394907300943933 := by
  unfold tailWord_6391413
  simp only [CollatzResearch.WordTrace]
  refine ⟨233113983194009742281466893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155409322129339828187644595 233113983194009742281466893)
  ·
    refine ⟨87417743697753653355550085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233113983194009742281466893 87417743697753653355550085)
    ·
      refine ⟨16390826943328810004165641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87417743697753653355550085 16390826943328810004165641)
      ·
        refine ⟨12293120207496607503124231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16390826943328810004165641 12293120207496607503124231)
        ·
          refine ⟨18439680311244911254686347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12293120207496607503124231 18439680311244911254686347)
          ·
            refine ⟨27659520466867366882029521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18439680311244911254686347 27659520466867366882029521)
            ·
              refine ⟨20744640350150525161522141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27659520466867366882029521 20744640350150525161522141)
              ·
                refine ⟨7779240131306446935570803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20744640350150525161522141 7779240131306446935570803)
                ·
                  refine ⟨11668860196959670403356205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7779240131306446935570803 11668860196959670403356205)
                  ·
                    refine ⟨4375822573859876401258577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11668860196959670403356205 4375822573859876401258577)
                    ·
                      refine ⟨3281866930394907300943933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4375822573859876401258577 3281866930394907300943933)
                      ·
                        rfl

theorem cell23_6391413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_6391413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6391413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6391413 prefixEnd_6391413 := by exact prefixLift 6391413
  have htrace : WordTrace (prefixWord ++ tailWord_6391413) baseStart_6391413 baseEnd_6391413 := by
    simpa [prefixWord, tailWord_6391413, baseEnd_6391413] using wordTrace_append hprefix tailTrace_6391413
  have hstable : (prefixWord ++ tailWord_6391413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6391413).length < 2 ^ (prefixWord ++ tailWord_6391413).sum := by decide
  have hdescent : baseEnd_6391413 < baseStart_6391413 := by decide
  rcases family_descends (prefixWord ++ tailWord_6391413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6391464 : List Nat := [2, 1, 7, 1, 1, 1, 3, 1, 1, 3, 2]
def baseStart_6391464 : Nat := 118140960795 + 6391464 * 2 ^ 59
def prefixEnd_6391464 : Nat := 4983230072969 + 3 ^ 40 * 6391464 * 2
def baseEnd_6391464 : Nat := 3281893117908286601406199

theorem tailTrace_6391464 : CollatzResearch.WordTrace tailWord_6391464 prefixEnd_6391464 3281893117908286601406199 := by
  unfold tailWord_6391464
  simp only [CollatzResearch.WordTrace]
  refine ⟨116557921658412488995786723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155410562211216651994382297 116557921658412488995786723)
  ·
    refine ⟨174836882487618733493680085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116557921658412488995786723 174836882487618733493680085)
    ·
      refine ⟨4097739433303564066258127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 174836882487618733493680085 4097739433303564066258127)
      ·
        refine ⟨6146609149955346099387191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4097739433303564066258127 6146609149955346099387191)
        ·
          refine ⟨9219913724933019149080787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6146609149955346099387191 9219913724933019149080787)
          ·
            refine ⟨13829870587399528723621181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9219913724933019149080787 13829870587399528723621181)
            ·
              refine ⟨5186201470274823271357943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13829870587399528723621181 5186201470274823271357943)
              ·
                refine ⟨7779302205412234907036915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5186201470274823271357943 7779302205412234907036915)
                ·
                  refine ⟨11668953308118352360555373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7779302205412234907036915 11668953308118352360555373)
                  ·
                    refine ⟨4375857490544382135208265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11668953308118352360555373 4375857490544382135208265)
                    ·
                      refine ⟨3281893117908286601406199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4375857490544382135208265 3281893117908286601406199)
                      ·
                        rfl

theorem cell23_6391464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_6391464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6391464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6391464 prefixEnd_6391464 := by exact prefixLift 6391464
  have htrace : WordTrace (prefixWord ++ tailWord_6391464) baseStart_6391464 baseEnd_6391464 := by
    simpa [prefixWord, tailWord_6391464, baseEnd_6391464] using wordTrace_append hprefix tailTrace_6391464
  have hstable : (prefixWord ++ tailWord_6391464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6391464).length < 2 ^ (prefixWord ++ tailWord_6391464).sum := by decide
  have hdescent : baseEnd_6391464 < baseStart_6391464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6391464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6391472 : List Nat := [2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 5]
def baseStart_6391472 : Nat := 118140960795 + 6391472 * 2 ^ 59
def prefixEnd_6391472 : Nat := 4983230072969 + 3 ^ 40 * 6391472 * 2
def baseEnd_6391472 : Nat := 3281897225753522570106161

theorem tailTrace_6391472 : CollatzResearch.WordTrace tailWord_6391472 prefixEnd_6391472 3281897225753522570106161 := by
  unfold tailWord_6391472
  simp only [CollatzResearch.WordTrace]
  refine ⟨116558067550397997678932335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155410756733863996905243113 116558067550397997678932335)
  ·
    refine ⟨174837101325596996518398503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116558067550397997678932335 174837101325596996518398503)
    ·
      refine ⟨262255651988395494777597755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174837101325596996518398503 262255651988395494777597755)
      ·
        refine ⟨393383477982593242166396633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262255651988395494777597755 393383477982593242166396633)
        ·
          refine ⟨295037608486944931624797475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 393383477982593242166396633 295037608486944931624797475)
          ·
            refine ⟨442556412730417397437196213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295037608486944931624797475 442556412730417397437196213)
            ·
              refine ⟨41489663693476631009737145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 442556412730417397437196213 41489663693476631009737145)
              ·
                refine ⟨31117247770107473257302859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41489663693476631009737145 31117247770107473257302859)
                ·
                  refine ⟨46675871655161209885954289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31117247770107473257302859 46675871655161209885954289)
                  ·
                    refine ⟨35006903741370907414465717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46675871655161209885954289 35006903741370907414465717)
                    ·
                      refine ⟨3281897225753522570106161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35006903741370907414465717 3281897225753522570106161)
                      ·
                        rfl

theorem cell23_6391472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 5].length) (baseStart_6391472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6391472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6391472 prefixEnd_6391472 := by exact prefixLift 6391472
  have htrace : WordTrace (prefixWord ++ tailWord_6391472) baseStart_6391472 baseEnd_6391472 := by
    simpa [prefixWord, tailWord_6391472, baseEnd_6391472] using wordTrace_append hprefix tailTrace_6391472
  have hstable : (prefixWord ++ tailWord_6391472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6391472).length < 2 ^ (prefixWord ++ tailWord_6391472).sum := by decide
  have hdescent : baseEnd_6391472 < baseStart_6391472 := by decide
  rcases family_descends (prefixWord ++ tailWord_6391472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6391479 : List Nat := [1, 1, 3, 1, 5, 1, 2, 2, 2, 5]
def baseStart_6391479 : Nat := 118140960795 + 6391479 * 2 ^ 59
def prefixEnd_6391479 : Nat := 4983230072969 + 3 ^ 40 * 6391479 * 2
def baseEnd_6391479 : Nat := 1093966940039368014239543

theorem tailTrace_6391479 : CollatzResearch.WordTrace tailWord_6391479 prefixEnd_6391479 1093966940039368014239543 := by
  unfold tailWord_6391479
  simp only [CollatzResearch.WordTrace]
  refine ⟨233116390411770635553369491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155410926941180423702246327 233116390411770635553369491)
  ·
    refine ⟨349674585617655953330054237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233116390411770635553369491 349674585617655953330054237)
    ·
      refine ⟨131127969606620982498770339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 349674585617655953330054237 131127969606620982498770339)
      ·
        refine ⟨196691954409931473748155509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131127969606620982498770339 196691954409931473748155509)
        ·
          refine ⟨18439870725931075663889579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 196691954409931473748155509 18439870725931075663889579)
          ·
            refine ⟨27659806088896613495834369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18439870725931075663889579 27659806088896613495834369)
            ·
              refine ⟨20744854566672460121875777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27659806088896613495834369 20744854566672460121875777)
              ·
                refine ⟨15558640925004345091406833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20744854566672460121875777 15558640925004345091406833)
                ·
                  refine ⟨11668980693753258818555125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15558640925004345091406833 11668980693753258818555125)
                  ·
                    refine ⟨1093966940039368014239543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11668980693753258818555125 1093966940039368014239543)
                    ·
                      rfl

theorem cell23_6391479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 2, 2, 5].length) (baseStart_6391479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6391479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6391479 prefixEnd_6391479 := by exact prefixLift 6391479
  have htrace : WordTrace (prefixWord ++ tailWord_6391479) baseStart_6391479 baseEnd_6391479 := by
    simpa [prefixWord, tailWord_6391479, baseEnd_6391479] using wordTrace_append hprefix tailTrace_6391479
  have hstable : (prefixWord ++ tailWord_6391479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6391479).length < 2 ^ (prefixWord ++ tailWord_6391479).sum := by decide
  have hdescent : baseEnd_6391479 < baseStart_6391479 := by decide
  rcases family_descends (prefixWord ++ tailWord_6391479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6391486 : List Nat := [4, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2]
def baseStart_6391486 : Nat := 118140960795 + 6391486 * 2 ^ 59
def prefixEnd_6391486 : Nat := 4983230072969 + 3 ^ 40 * 6391486 * 2
def baseEnd_6391486 : Nat := 3281904414482685515331097

theorem tailTrace_6391486 : CollatzResearch.WordTrace tailWord_6391486 prefixEnd_6391486 3281904414482685515331097 := by
  unfold tailWord_6391486
  simp only [CollatzResearch.WordTrace]
  refine ⟨29139580715343159468609289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155411097148496850499249541 29139580715343159468609289)
  ·
    refine ⟨21854685536507369601456967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29139580715343159468609289 21854685536507369601456967)
    ·
      refine ⟨32782028304761054402185451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21854685536507369601456967 32782028304761054402185451)
      ·
        refine ⟨49173042457141581603278177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32782028304761054402185451 49173042457141581603278177)
        ·
          refine ⟨36879781842856186202458633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49173042457141581603278177 36879781842856186202458633)
          ·
            refine ⟨27659836382142139651843975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36879781842856186202458633 27659836382142139651843975)
            ·
              refine ⟨41489754573213209477765963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27659836382142139651843975 41489754573213209477765963)
              ·
                refine ⟨62234631859819814216648945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41489754573213209477765963 62234631859819814216648945)
                ·
                  refine ⟨46675973894864860662486709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62234631859819814216648945 46675973894864860662486709)
                  ·
                    refine ⟨4375872552643580687108129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46675973894864860662486709 4375872552643580687108129)
                    ·
                      refine ⟨3281904414482685515331097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4375872552643580687108129 3281904414482685515331097)
                      ·
                        rfl

theorem cell23_6391486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2].length) (baseStart_6391486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6391486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6391486 prefixEnd_6391486 := by exact prefixLift 6391486
  have htrace : WordTrace (prefixWord ++ tailWord_6391486) baseStart_6391486 baseEnd_6391486 := by
    simpa [prefixWord, tailWord_6391486, baseEnd_6391486] using wordTrace_append hprefix tailTrace_6391486
  have hstable : (prefixWord ++ tailWord_6391486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6391486).length < 2 ^ (prefixWord ++ tailWord_6391486).sum := by decide
  have hdescent : baseEnd_6391486 < baseStart_6391486 := by decide
  rcases family_descends (prefixWord ++ tailWord_6391486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6391490 : List Nat := [3, 5, 1, 2, 1, 1, 1, 1, 2, 2, 4]
def baseStart_6391490 : Nat := 118140960795 + 6391490 * 2 ^ 59
def prefixEnd_6391490 : Nat := 4983230072969 + 3 ^ 40 * 6391490 * 2
def baseEnd_6391490 : Nat := 3281906468405303499681079

theorem tailTrace_6391490 : CollatzResearch.WordTrace tailWord_6391490 prefixEnd_6391490 3281906468405303499681079 := by
  unfold tailWord_6391490
  simp only [CollatzResearch.WordTrace]
  refine ⟨58279197903682696108004981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155411194409820522954679949 58279197903682696108004981)
  ·
    refine ⟨5463674803470252760125467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58279197903682696108004981 5463674803470252760125467)
    ·
      refine ⟨8195512205205379140188201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5463674803470252760125467 8195512205205379140188201)
      ·
        refine ⟨6146634153904034355141151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8195512205205379140188201 6146634153904034355141151)
        ·
          refine ⟨9219951230856051532711727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6146634153904034355141151 9219951230856051532711727)
          ·
            refine ⟨13829926846284077299067591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9219951230856051532711727 13829926846284077299067591)
            ·
              refine ⟨20744890269426115948601387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13829926846284077299067591 20744890269426115948601387)
              ·
                refine ⟨31117335404139173922902081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20744890269426115948601387 31117335404139173922902081)
                ·
                  refine ⟨23338001553104380442176561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31117335404139173922902081 23338001553104380442176561)
                  ·
                    refine ⟨17503501164828285331632421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23338001553104380442176561 17503501164828285331632421)
                    ·
                      refine ⟨3281906468405303499681079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17503501164828285331632421 3281906468405303499681079)
                      ·
                        rfl

theorem cell23_6391490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_6391490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6391490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6391490 prefixEnd_6391490 := by exact prefixLift 6391490
  have htrace : WordTrace (prefixWord ++ tailWord_6391490) baseStart_6391490 baseEnd_6391490 := by
    simpa [prefixWord, tailWord_6391490, baseEnd_6391490] using wordTrace_append hprefix tailTrace_6391490
  have hstable : (prefixWord ++ tailWord_6391490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6391490).length < 2 ^ (prefixWord ++ tailWord_6391490).sum := by decide
  have hdescent : baseEnd_6391490 < baseStart_6391490 := by decide
  rcases family_descends (prefixWord ++ tailWord_6391490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6391519 : List Nat := [1, 1, 2, 3, 2, 2, 3, 1, 1, 4, 3]
def baseStart_6391519 : Nat := 118140960795 + 6391519 * 2 ^ 59
def prefixEnd_6391519 : Nat := 4983230072969 + 3 ^ 40 * 6391519 * 2
def baseEnd_6391519 : Nat := 3281921359344283886218445

theorem tailTrace_6391519 : CollatzResearch.WordTrace tailWord_6391519 prefixEnd_6391519 3281921359344283886218445 := by
  unfold tailWord_6391519
  simp only [CollatzResearch.WordTrace]
  refine ⟨233117849331625722384825611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155411899554417148256550407 233117849331625722384825611)
  ·
    refine ⟨349676773997438583577238417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233117849331625722384825611 349676773997438583577238417)
    ·
      refine ⟨262257580498078937682928813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 349676773997438583577238417 262257580498078937682928813)
      ·
        refine ⟨98346592686779601631098305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 262257580498078937682928813 98346592686779601631098305)
        ·
          refine ⟨73759944515084701223323729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98346592686779601631098305 73759944515084701223323729)
          ·
            refine ⟨55319958386313525917492797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73759944515084701223323729 55319958386313525917492797)
            ·
              refine ⟨20744984394867572219059799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55319958386313525917492797 20744984394867572219059799)
              ·
                refine ⟨31117476592301358328589699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20744984394867572219059799 31117476592301358328589699)
                ·
                  refine ⟨46676214888452037492884549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31117476592301358328589699 46676214888452037492884549)
                  ·
                    refine ⟨8751790291584757029915853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46676214888452037492884549 8751790291584757029915853)
                    ·
                      refine ⟨3281921359344283886218445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8751790291584757029915853 3281921359344283886218445)
                      ·
                        rfl

theorem cell23_6391519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 4, 3].length) (baseStart_6391519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6391519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6391519 prefixEnd_6391519 := by exact prefixLift 6391519
  have htrace : WordTrace (prefixWord ++ tailWord_6391519) baseStart_6391519 baseEnd_6391519 := by
    simpa [prefixWord, tailWord_6391519, baseEnd_6391519] using wordTrace_append hprefix tailTrace_6391519
  have hstable : (prefixWord ++ tailWord_6391519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6391519).length < 2 ^ (prefixWord ++ tailWord_6391519).sum := by decide
  have hdescent : baseEnd_6391519 < baseStart_6391519 := by decide
  rcases family_descends (prefixWord ++ tailWord_6391519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6391539 : List Nat := [1, 1, 1, 2, 2, 3, 5, 2, 6]
def baseStart_6391539 : Nat := 118140960795 + 6391539 * 2 ^ 59
def prefixEnd_6391539 : Nat := 4983230072969 + 3 ^ 40 * 6391539 * 2
def baseEnd_6391539 : Nat := 364659069884152645329817

theorem tailTrace_6391539 : CollatzResearch.WordTrace tailWord_6391539 prefixEnd_6391539 364659069884152645329817 := by
  unfold tailWord_6391539
  simp only [CollatzResearch.WordTrace]
  refine ⟨233118578791553265800553671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155412385861035510533702447 233118578791553265800553671)
  ·
    refine ⟨349677868187329898700830507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233118578791553265800553671 349677868187329898700830507)
    ·
      refine ⟨524516802280994848051245761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349677868187329898700830507 524516802280994848051245761)
      ·
        refine ⟨393387601710746136038434321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 524516802280994848051245761 393387601710746136038434321)
        ·
          refine ⟨295040701283059602028825741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 393387601710746136038434321 295040701283059602028825741)
          ·
            refine ⟨110640262981147350760809653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 295040701283059602028825741 110640262981147350760809653)
            ·
              refine ⟨10372524654482564133825905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 110640262981147350760809653 10372524654482564133825905)
              ·
                refine ⟨7779393490861923100369429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10372524654482564133825905 7779393490861923100369429)
                ·
                  refine ⟨364659069884152645329817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7779393490861923100369429 364659069884152645329817)
                  ·
                    rfl

theorem cell23_6391539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 2, 6].length) (baseStart_6391539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6391539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6391539 prefixEnd_6391539 := by exact prefixLift 6391539
  have htrace : WordTrace (prefixWord ++ tailWord_6391539) baseStart_6391539 baseEnd_6391539 := by
    simpa [prefixWord, tailWord_6391539, baseEnd_6391539] using wordTrace_append hprefix tailTrace_6391539
  have hstable : (prefixWord ++ tailWord_6391539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6391539).length < 2 ^ (prefixWord ++ tailWord_6391539).sum := by decide
  have hdescent : baseEnd_6391539 < baseStart_6391539 := by decide
  rcases family_descends (prefixWord ++ tailWord_6391539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6391576 : List Nat := [2, 1, 2, 3, 1, 1, 4, 1, 1, 5, 2]
def baseStart_6391576 : Nat := 118140960795 + 6391576 * 2 ^ 59
def prefixEnd_6391576 : Nat := 4983230072969 + 3 ^ 40 * 6391576 * 2
def baseEnd_6391576 : Nat := 3281950627741590163205683

theorem tailTrace_6391576 : CollatzResearch.WordTrace tailWord_6391576 prefixEnd_6391576 3281950627741590163205683 := by
  unfold tailWord_6391576
  simp only [CollatzResearch.WordTrace]
  refine ⟨116559964146209610559825291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155413285528279480746433721 116559964146209610559825291)
  ·
    refine ⟨174839946219314415839737937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116559964146209610559825291 174839946219314415839737937)
    ·
      refine ⟨131129959664485811879803453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174839946219314415839737937 131129959664485811879803453)
      ·
        refine ⟨49173734874182179454926295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131129959664485811879803453 49173734874182179454926295)
        ·
          refine ⟨73760602311273269182389443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49173734874182179454926295 73760602311273269182389443)
          ·
            refine ⟨110640903466909903773584165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73760602311273269182389443 110640903466909903773584165)
            ·
              refine ⟨20745169400045606957547031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110640903466909903773584165 20745169400045606957547031)
              ·
                refine ⟨31117754100068410436320547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20745169400045606957547031 31117754100068410436320547)
                ·
                  refine ⟨46676631150102615654480821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31117754100068410436320547 46676631150102615654480821)
                  ·
                    refine ⟨4375934170322120217607577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46676631150102615654480821 4375934170322120217607577)
                    ·
                      refine ⟨3281950627741590163205683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4375934170322120217607577 3281950627741590163205683)
                      ·
                        rfl

theorem cell23_6391576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 1, 5, 2].length) (baseStart_6391576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6391576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6391576 prefixEnd_6391576 := by exact prefixLift 6391576
  have htrace : WordTrace (prefixWord ++ tailWord_6391576) baseStart_6391576 baseEnd_6391576 := by
    simpa [prefixWord, tailWord_6391576, baseEnd_6391576] using wordTrace_append hprefix tailTrace_6391576
  have hstable : (prefixWord ++ tailWord_6391576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6391576).length < 2 ^ (prefixWord ++ tailWord_6391576).sum := by decide
  have hdescent : baseEnd_6391576 < baseStart_6391576 := by decide
  rcases family_descends (prefixWord ++ tailWord_6391576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6391586 : List Nat := [3, 3, 1, 1, 2, 1, 1, 5, 1, 5]
def baseStart_6391586 : Nat := 118140960795 + 6391586 * 2 ^ 59
def prefixEnd_6391586 : Nat := 4983230072969 + 3 ^ 40 * 6391586 * 2
def baseEnd_6391586 : Nat := 1093985254182711708026879

theorem tailTrace_6391586 : CollatzResearch.WordTrace tailWord_6391586 prefixEnd_6391586 1093985254182711708026879 := by
  unfold tailWord_6391586
  simp only [CollatzResearch.WordTrace]
  refine ⟨58280073255595748206878653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155413528681588661885009741 58280073255595748206878653)
  ·
    refine ⟨21855027470848405577579495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58280073255595748206878653 21855027470848405577579495)
    ·
      refine ⟨32782541206272608366369243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21855027470848405577579495 32782541206272608366369243)
      ·
        refine ⟨49173811809408912549553865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32782541206272608366369243 49173811809408912549553865)
        ·
          refine ⟨36880358857056684412165399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49173811809408912549553865 36880358857056684412165399)
          ·
            refine ⟨55320538285585026618248099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36880358857056684412165399 55320538285585026618248099)
            ·
              refine ⟨82980807428377539927372149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55320538285585026618248099 82980807428377539927372149)
              ·
                refine ⟨7779450696410394368191139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82980807428377539927372149 7779450696410394368191139)
                ·
                  refine ⟨11669176044615591552286709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7779450696410394368191139 11669176044615591552286709)
                  ·
                    refine ⟨1093985254182711708026879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11669176044615591552286709 1093985254182711708026879)
                    ·
                      rfl

theorem cell23_6391586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_6391586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6391586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6391586 prefixEnd_6391586 := by exact prefixLift 6391586
  have htrace : WordTrace (prefixWord ++ tailWord_6391586) baseStart_6391586 baseEnd_6391586 := by
    simpa [prefixWord, tailWord_6391586, baseEnd_6391586] using wordTrace_append hprefix tailTrace_6391586
  have hstable : (prefixWord ++ tailWord_6391586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6391586).length < 2 ^ (prefixWord ++ tailWord_6391586).sum := by decide
  have hdescent : baseEnd_6391586 < baseStart_6391586 := by decide
  rcases family_descends (prefixWord ++ tailWord_6391586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6391619 : List Nat := [1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 6]
def baseStart_6391619 : Nat := 118140960795 + 6391619 * 2 ^ 59
def prefixEnd_6391619 : Nat := 4983230072969 + 3 ^ 40 * 6391619 * 2
def baseEnd_6391619 : Nat := 3281972707409733494967985

theorem tailTrace_6391619 : CollatzResearch.WordTrace tailWord_6391619 prefixEnd_6391619 3281972707409733494967985 := by
  unfold tailWord_6391619
  simp only [CollatzResearch.WordTrace]
  refine ⟨233121496631263439463465911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155414331087508959642310607 233121496631263439463465911)
  ·
    refine ⟨349682244946895159195198867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233121496631263439463465911 349682244946895159195198867)
    ·
      refine ⟨524523367420342738792798301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349682244946895159195198867 524523367420342738792798301)
      ·
        refine ⟨196696262782628527047299363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 524523367420342738792798301 196696262782628527047299363)
        ·
          refine ⟨295044394173942790570949045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196696262782628527047299363 295044394173942790570949045)
          ·
            refine ⟨27660411953807136616026473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 295044394173942790570949045 27660411953807136616026473)
            ·
              refine ⟨20745308965355352462019855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27660411953807136616026473 20745308965355352462019855)
              ·
                refine ⟨31117963448033028693029783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20745308965355352462019855 31117963448033028693029783)
                ·
                  refine ⟨46676945172049543039544675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31117963448033028693029783 46676945172049543039544675)
                  ·
                    refine ⟨70015417758074314559317013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46676945172049543039544675 70015417758074314559317013)
                    ·
                      refine ⟨3281972707409733494967985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70015417758074314559317013 3281972707409733494967985)
                      ·
                        rfl

theorem cell23_6391619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 6].length) (baseStart_6391619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6391619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6391619 prefixEnd_6391619 := by exact prefixLift 6391619
  have htrace : WordTrace (prefixWord ++ tailWord_6391619) baseStart_6391619 baseEnd_6391619 := by
    simpa [prefixWord, tailWord_6391619, baseEnd_6391619] using wordTrace_append hprefix tailTrace_6391619
  have hstable : (prefixWord ++ tailWord_6391619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6391619).length < 2 ^ (prefixWord ++ tailWord_6391619).sum := by decide
  have hdescent : baseEnd_6391619 < baseStart_6391619 := by decide
  rcases family_descends (prefixWord ++ tailWord_6391619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6391623 : List Nat := [1, 1, 4, 1, 2, 1, 2, 4, 3, 2, 2]
def baseStart_6391623 : Nat := 118140960795 + 6391623 * 2 ^ 59
def prefixEnd_6391623 : Nat := 4983230072969 + 3 ^ 40 * 6391623 * 2
def baseEnd_6391623 : Nat := 3281974761332351479317967

theorem tailTrace_6391623 : CollatzResearch.WordTrace tailWord_6391623 prefixEnd_6391623 3281974761332351479317967 := by
  unfold tailWord_6391623
  simp only [CollatzResearch.WordTrace]
  refine ⟨233121642523248948146611523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155414428348832632097741015 233121642523248948146611523)
  ·
    refine ⟨349682463784873422219917285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233121642523248948146611523 349682463784873422219917285)
    ·
      refine ⟨65565461959663766666234491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 349682463784873422219917285 65565461959663766666234491)
      ·
        refine ⟨98348192939495649999351737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65565461959663766666234491 98348192939495649999351737)
        ·
          refine ⟨73761144704621737499513803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98348192939495649999351737 73761144704621737499513803)
          ·
            refine ⟨110641717056932606249270705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73761144704621737499513803 110641717056932606249270705)
            ·
              refine ⟨82981287792699454686953029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110641717056932606249270705 82981287792699454686953029)
              ·
                refine ⟨15558991461131147753803693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82981287792699454686953029 15558991461131147753803693)
                ·
                  refine ⟨5834621797924180407676385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15558991461131147753803693 5834621797924180407676385)
                  ·
                    refine ⟨4375966348443135305757289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5834621797924180407676385 4375966348443135305757289)
                    ·
                      refine ⟨3281974761332351479317967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4375966348443135305757289 3281974761332351479317967)
                      ·
                        rfl

theorem cell23_6391623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4, 3, 2, 2].length) (baseStart_6391623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6391623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6391623 prefixEnd_6391623 := by exact prefixLift 6391623
  have htrace : WordTrace (prefixWord ++ tailWord_6391623) baseStart_6391623 baseEnd_6391623 := by
    simpa [prefixWord, tailWord_6391623, baseEnd_6391623] using wordTrace_append hprefix tailTrace_6391623
  have hstable : (prefixWord ++ tailWord_6391623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6391623).length < 2 ^ (prefixWord ++ tailWord_6391623).sum := by decide
  have hdescent : baseEnd_6391623 < baseStart_6391623 := by decide
  rcases family_descends (prefixWord ++ tailWord_6391623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6391626 : List Nat := [3, 1, 2, 1, 1, 1, 5, 1, 3, 2, 3]
def baseStart_6391626 : Nat := 118140960795 + 6391626 * 2 ^ 59
def prefixEnd_6391626 : Nat := 4983230072969 + 3 ^ 40 * 6391626 * 2
def baseEnd_6391626 : Nat := 3281976301774314967580453

theorem tailTrace_6391626 : CollatzResearch.WordTrace tailWord_6391626 prefixEnd_6391626 3281976301774314967580453 := by
  unfold tailWord_6391626
  simp only [CollatzResearch.WordTrace]
  refine ⟨58280437985559519914742683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155414501294825386439313821 58280437985559519914742683)
  ·
    refine ⟨87420656978339279872114025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58280437985559519914742683 87420656978339279872114025)
    ·
      refine ⟨65565492733754459904085519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87420656978339279872114025 65565492733754459904085519)
      ·
        refine ⟨98348239100631689856128279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65565492733754459904085519 98348239100631689856128279)
        ·
          refine ⟨147522358650947534784192419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98348239100631689856128279 147522358650947534784192419)
          ·
            refine ⟨221283537976421302176288629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147522358650947534784192419 221283537976421302176288629)
            ·
              refine ⟨20745331685289497079027059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 221283537976421302176288629 20745331685289497079027059)
              ·
                refine ⟨31117997527934245618540589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20745331685289497079027059 31117997527934245618540589)
                ·
                  refine ⟨11669249072975342106952721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31117997527934245618540589 11669249072975342106952721)
                  ·
                    refine ⟨8751936804731506580214541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11669249072975342106952721 8751936804731506580214541)
                    ·
                      refine ⟨3281976301774314967580453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8751936804731506580214541 3281976301774314967580453)
                      ·
                        rfl

theorem cell23_6391626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 3, 2, 3].length) (baseStart_6391626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6391626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6391626 prefixEnd_6391626 := by exact prefixLift 6391626
  have htrace : WordTrace (prefixWord ++ tailWord_6391626) baseStart_6391626 baseEnd_6391626 := by
    simpa [prefixWord, tailWord_6391626, baseEnd_6391626] using wordTrace_append hprefix tailTrace_6391626
  have hstable : (prefixWord ++ tailWord_6391626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6391626).length < 2 ^ (prefixWord ++ tailWord_6391626).sum := by decide
  have hdescent : baseEnd_6391626 < baseStart_6391626 := by decide
  rcases family_descends (prefixWord ++ tailWord_6391626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6391636 : List Nat := [2, 4, 1, 1, 3, 1, 1, 1, 3, 2, 4]
def baseStart_6391636 : Nat := 118140960795 + 6391636 * 2 ^ 59
def prefixEnd_6391636 : Nat := 4983230072969 + 3 ^ 40 * 6391636 * 2
def baseEnd_6391636 : Nat := 3281981436580859928455407

theorem tailTrace_6391636 : CollatzResearch.WordTrace tailWord_6391636 prefixEnd_6391636 3281981436580859928455407 := by
  unfold tailWord_6391636
  simp only [CollatzResearch.WordTrace]
  refine ⟨116561058336100925683417381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155414744448134567577889841 116561058336100925683417381)
  ·
    refine ⟨21855198438018923565640759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116561058336100925683417381 21855198438018923565640759)
    ·
      refine ⟨32782797657028385348461139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21855198438018923565640759 32782797657028385348461139)
      ·
        refine ⟨49174196485542578022691709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32782797657028385348461139 49174196485542578022691709)
        ·
          refine ⟨18440323682078466758509391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49174196485542578022691709 18440323682078466758509391)
          ·
            refine ⟨27660485523117700137764087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18440323682078466758509391 27660485523117700137764087)
            ·
              refine ⟨41490728284676550206646131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27660485523117700137764087 41490728284676550206646131)
              ·
                refine ⟨62236092427014825309969197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41490728284676550206646131 62236092427014825309969197)
                ·
                  refine ⟨23338534660130559491238449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62236092427014825309969197 23338534660130559491238449)
                  ·
                    refine ⟨17503900995097919618428837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23338534660130559491238449 17503900995097919618428837)
                    ·
                      refine ⟨3281981436580859928455407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17503900995097919618428837 3281981436580859928455407)
                      ·
                        rfl

theorem cell23_6391636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_6391636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6391636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6391636 prefixEnd_6391636 := by exact prefixLift 6391636
  have htrace : WordTrace (prefixWord ++ tailWord_6391636) baseStart_6391636 baseEnd_6391636 := by
    simpa [prefixWord, tailWord_6391636, baseEnd_6391636] using wordTrace_append hprefix tailTrace_6391636
  have hstable : (prefixWord ++ tailWord_6391636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6391636).length < 2 ^ (prefixWord ++ tailWord_6391636).sum := by decide
  have hdescent : baseEnd_6391636 < baseStart_6391636 := by decide
  rcases family_descends (prefixWord ++ tailWord_6391636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6391650 : List Nat := [3, 3, 2, 1, 2, 2, 2, 2, 2, 4]
def baseStart_6391650 : Nat := 118140960795 + 6391650 * 2 ^ 59
def prefixEnd_6391650 : Nat := 4983230072969 + 3 ^ 40 * 6391650 * 2
def baseEnd_6391650 : Nat := 1093996208436674291226781

theorem tailTrace_6391650 : CollatzResearch.WordTrace tailWord_6391650 prefixEnd_6391650 1093996208436674291226781 := by
  unfold tailWord_6391650
  simp only [CollatzResearch.WordTrace]
  refine ⟨58280656823537782939461101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155415084862767421171896269 58280656823537782939461101)
  ·
    refine ⟨21855246308826668602297913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58280656823537782939461101 21855246308826668602297913)
    ·
      refine ⟨16391434731620001451723435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21855246308826668602297913 16391434731620001451723435)
      ·
        refine ⟨24587152097430002177585153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16391434731620001451723435 24587152097430002177585153)
        ·
          refine ⟨18440364073072501633188865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24587152097430002177585153 18440364073072501633188865)
          ·
            refine ⟨13830273054804376224891649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18440364073072501633188865 13830273054804376224891649)
            ·
              refine ⟨10372704791103282168668737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13830273054804376224891649 10372704791103282168668737)
              ·
                refine ⟨7779528593327461626501553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10372704791103282168668737 7779528593327461626501553)
                ·
                  refine ⟨5834646444995596219876165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7779528593327461626501553 5834646444995596219876165)
                  ·
                    refine ⟨1093996208436674291226781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5834646444995596219876165 1093996208436674291226781)
                    ·
                      rfl

theorem cell23_6391650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_6391650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6391650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6391650 prefixEnd_6391650 := by exact prefixLift 6391650
  have htrace : WordTrace (prefixWord ++ tailWord_6391650) baseStart_6391650 baseEnd_6391650 := by
    simpa [prefixWord, tailWord_6391650, baseEnd_6391650] using wordTrace_append hprefix tailTrace_6391650
  have hstable : (prefixWord ++ tailWord_6391650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6391650).length < 2 ^ (prefixWord ++ tailWord_6391650).sum := by decide
  have hdescent : baseEnd_6391650 < baseStart_6391650 := by decide
  rcases family_descends (prefixWord ++ tailWord_6391650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6391656 : List Nat := [2, 1, 4, 2, 1, 1, 1, 2, 3, 3, 3]
def baseStart_6391656 : Nat := 118140960795 + 6391656 * 2 ^ 59
def prefixEnd_6391656 : Nat := 4983230072969 + 3 ^ 40 * 6391656 * 2
def baseEnd_6391656 : Nat := 3281991706193949850205315

theorem tailTrace_6391656 : CollatzResearch.WordTrace tailWord_6391656 prefixEnd_6391656 3281991706193949850205315 := by
  unfold tailWord_6391656
  simp only [CollatzResearch.WordTrace]
  refine ⟨116561423066064697391281411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155415230754752929855041881 116561423066064697391281411)
  ·
    refine ⟨174842134599097046086922117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116561423066064697391281411 174842134599097046086922117)
    ·
      refine ⟨32782900237330696141297897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 174842134599097046086922117 32782900237330696141297897)
      ·
        refine ⟨24587175177998022105973423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32782900237330696141297897 24587175177998022105973423)
        ·
          refine ⟨36880762766997033158960135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24587175177998022105973423 36880762766997033158960135)
          ·
            refine ⟨55321144150495549738440203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36880762766997033158960135 55321144150495549738440203)
            ·
              refine ⟨82981716225743324607660305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55321144150495549738440203 82981716225743324607660305)
              ·
                refine ⟨62236287169307493455745229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82981716225743324607660305 62236287169307493455745229)
                ·
                  refine ⟨23338607688490310045904461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62236287169307493455745229 23338607688490310045904461)
                  ·
                    refine ⟨8751977883183866267214173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23338607688490310045904461 8751977883183866267214173)
                    ·
                      refine ⟨3281991706193949850205315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8751977883183866267214173 3281991706193949850205315)
                      ·
                        rfl

theorem cell23_6391656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_6391656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6391656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6391656 prefixEnd_6391656 := by exact prefixLift 6391656
  have htrace : WordTrace (prefixWord ++ tailWord_6391656) baseStart_6391656 baseEnd_6391656 := by
    simpa [prefixWord, tailWord_6391656, baseEnd_6391656] using wordTrace_append hprefix tailTrace_6391656
  have hstable : (prefixWord ++ tailWord_6391656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6391656).length < 2 ^ (prefixWord ++ tailWord_6391656).sum := by decide
  have hdescent : baseEnd_6391656 < baseStart_6391656 := by decide
  rcases family_descends (prefixWord ++ tailWord_6391656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6391670 : List Nat := [5, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4]
def baseStart_6391670 : Nat := 118140960795 + 6391670 * 2 ^ 59
def prefixEnd_6391670 : Nat := 4983230072969 + 3 ^ 40 * 6391670 * 2
def baseEnd_6391670 : Nat := 3281998894923112795430251

theorem tailTrace_6391670 : CollatzResearch.WordTrace tailWord_6391670 prefixEnd_6391670 3281998894923112795430251 := by
  unfold tailWord_6391670
  simp only [CollatzResearch.WordTrace]
  refine ⟨14570209797129917198348279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 155415571169385783449048309 14570209797129917198348279)
  ·
    refine ⟨21855314695694875797522419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14570209797129917198348279 21855314695694875797522419)
    ·
      refine ⟨32782972043542313696283629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21855314695694875797522419 32782972043542313696283629)
      ·
        refine ⟨12293614516328367636106361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32782972043542313696283629 12293614516328367636106361)
        ·
          refine ⟨9220210887246275727079771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12293614516328367636106361 9220210887246275727079771)
          ·
            refine ⟨13830316330869413590619657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9220210887246275727079771 13830316330869413590619657)
            ·
              refine ⟨10372737248152060192964743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13830316330869413590619657 10372737248152060192964743)
              ·
                refine ⟨15559105872228090289447115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10372737248152060192964743 15559105872228090289447115)
                ·
                  refine ⟨23338658808342135434170673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15559105872228090289447115 23338658808342135434170673)
                  ·
                    refine ⟨17503994106256601575628005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23338658808342135434170673 17503994106256601575628005)
                    ·
                      refine ⟨3281998894923112795430251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17503994106256601575628005 3281998894923112795430251)
                      ·
                        rfl

theorem cell23_6391670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_6391670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6391670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6391670 prefixEnd_6391670 := by exact prefixLift 6391670
  have htrace : WordTrace (prefixWord ++ tailWord_6391670) baseStart_6391670 baseEnd_6391670 := by
    simpa [prefixWord, tailWord_6391670, baseEnd_6391670] using wordTrace_append hprefix tailTrace_6391670
  have hstable : (prefixWord ++ tailWord_6391670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6391670).length < 2 ^ (prefixWord ++ tailWord_6391670).sum := by decide
  have hdescent : baseEnd_6391670 < baseStart_6391670 := by decide
  rcases family_descends (prefixWord ++ tailWord_6391670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6391673 : List Nat := [1, 2, 1, 3, 2, 2, 1, 5, 2, 1, 3]
def baseStart_6391673 : Nat := 118140960795 + 6391673 * 2 ^ 59
def prefixEnd_6391673 : Nat := 4983230072969 + 3 ^ 40 * 6391673 * 2
def baseEnd_6391673 : Nat := 3282000435365076283692737

theorem tailTrace_6391673 : CollatzResearch.WordTrace tailWord_6391673 prefixEnd_6391673 3282000435365076283692737 := by
  unfold tailWord_6391673
  simp only [CollatzResearch.WordTrace]
  refine ⟨233123466173067806685931673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155415644115378537790621115 233123466173067806685931673)
  ·
    refine ⟨174842599629800855014448755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233123466173067806685931673 174842599629800855014448755)
    ·
      refine ⟨262263899444701282521673133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174842599629800855014448755 262263899444701282521673133)
      ·
        refine ⟨98348962291762980945627425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 262263899444701282521673133 98348962291762980945627425)
        ·
          refine ⟨73761721718822235709220569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98348962291762980945627425 73761721718822235709220569)
          ·
            refine ⟨55321291289116676781915427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73761721718822235709220569 55321291289116676781915427)
            ·
              refine ⟨82981936933675015172873141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55321291289116676781915427 82981936933675015172873141)
              ·
                refine ⟨7779556587532032672456857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82981936933675015172873141 7779556587532032672456857)
                ·
                  refine ⟨5834667440649024504342643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7779556587532032672456857 5834667440649024504342643)
                  ·
                    refine ⟨8752001160973536756513965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5834667440649024504342643 8752001160973536756513965)
                    ·
                      refine ⟨3282000435365076283692737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8752001160973536756513965 3282000435365076283692737)
                      ·
                        rfl

theorem cell23_6391673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 5, 2, 1, 3].length) (baseStart_6391673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6391673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6391673 prefixEnd_6391673 := by exact prefixLift 6391673
  have htrace : WordTrace (prefixWord ++ tailWord_6391673) baseStart_6391673 baseEnd_6391673 := by
    simpa [prefixWord, tailWord_6391673, baseEnd_6391673] using wordTrace_append hprefix tailTrace_6391673
  have hstable : (prefixWord ++ tailWord_6391673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6391673).length < 2 ^ (prefixWord ++ tailWord_6391673).sum := by decide
  have hdescent : baseEnd_6391673 < baseStart_6391673 := by decide
  rcases family_descends (prefixWord ++ tailWord_6391673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6391679 : List Nat := [1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 4]
def baseStart_6391679 : Nat := 118140960795 + 6391679 * 2 ^ 59
def prefixEnd_6391679 : Nat := 4983230072969 + 3 ^ 40 * 6391679 * 2
def baseEnd_6391679 : Nat := 3282003516249003260217709

theorem tailTrace_6391679 : CollatzResearch.WordTrace tailWord_6391679 prefixEnd_6391679 3282003516249003260217709 := by
  unfold tailWord_6391679
  simp only [CollatzResearch.WordTrace]
  refine ⟨233123685011046069710650091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155415790007364046473766727 233123685011046069710650091)
  ·
    refine ⟨349685527516569104565975137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233123685011046069710650091 349685527516569104565975137)
    ·
      refine ⟨262264145637426828424481353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 349685527516569104565975137 262264145637426828424481353)
      ·
        refine ⟨196698109228070121318361015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262264145637426828424481353 196698109228070121318361015)
        ·
          refine ⟨295047163842105181977541523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196698109228070121318361015 295047163842105181977541523)
          ·
            refine ⟨442570745763157772966312285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295047163842105181977541523 442570745763157772966312285)
            ·
              refine ⟨165964029661184164862367107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 442570745763157772966312285 165964029661184164862367107)
              ·
                refine ⟨248946044491776247293550661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165964029661184164862367107 248946044491776247293550661)
                ·
                  refine ⟨46677383342208046367540749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 248946044491776247293550661 46677383342208046367540749)
                  ·
                    refine ⟨17504018753328017387827781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46677383342208046367540749 17504018753328017387827781)
                    ·
                      refine ⟨3282003516249003260217709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17504018753328017387827781 3282003516249003260217709)
                      ·
                        rfl

theorem cell23_6391679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 4].length) (baseStart_6391679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6391679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6391679 prefixEnd_6391679 := by exact prefixLift 6391679
  have htrace : WordTrace (prefixWord ++ tailWord_6391679) baseStart_6391679 baseEnd_6391679 := by
    simpa [prefixWord, tailWord_6391679, baseEnd_6391679] using wordTrace_append hprefix tailTrace_6391679
  have hstable : (prefixWord ++ tailWord_6391679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6391679).length < 2 ^ (prefixWord ++ tailWord_6391679).sum := by decide
  have hdescent : baseEnd_6391679 < baseStart_6391679 := by decide
  rcases family_descends (prefixWord ++ tailWord_6391679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6391683 : List Nat := [1, 1, 1, 3, 4, 2, 2, 1, 3, 3, 2]
def baseStart_6391683 : Nat := 118140960795 + 6391683 * 2 ^ 59
def prefixEnd_6391683 : Nat := 4983230072969 + 3 ^ 40 * 6391683 * 2
def baseEnd_6391683 : Nat := 3282005570171621244567691

theorem tailTrace_6391683 : CollatzResearch.WordTrace tailWord_6391683 prefixEnd_6391683 3282005570171621244567691 := by
  unfold tailWord_6391683
  simp only [CollatzResearch.WordTrace]
  refine ⟨233123830903031578393795703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155415887268687718929197135 233123830903031578393795703)
  ·
    refine ⟨349685746354547367590693555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233123830903031578393795703 349685746354547367590693555)
    ·
      refine ⟨524528619531821051386040333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349685746354547367590693555 524528619531821051386040333)
      ·
        refine ⟨196698232324432894269765125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 524528619531821051386040333 196698232324432894269765125)
        ·
          refine ⟨36880918560831167675580961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 196698232324432894269765125 36880918560831167675580961)
          ·
            refine ⟨27660688920623375756685721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36880918560831167675580961 27660688920623375756685721)
            ·
              refine ⟨20745516690467531817514291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27660688920623375756685721 20745516690467531817514291)
              ·
                refine ⟨31118275035701297726271437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20745516690467531817514291 31118275035701297726271437)
                ·
                  refine ⟨11669353138387986647351789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31118275035701297726271437 11669353138387986647351789)
                  ·
                    refine ⟨4376007426895494992756921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11669353138387986647351789 4376007426895494992756921)
                    ·
                      refine ⟨3282005570171621244567691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4376007426895494992756921 3282005570171621244567691)
                      ·
                        rfl

theorem cell23_6391683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 3, 3, 2].length) (baseStart_6391683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6391683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6391683 prefixEnd_6391683 := by exact prefixLift 6391683
  have htrace : WordTrace (prefixWord ++ tailWord_6391683) baseStart_6391683 baseEnd_6391683 := by
    simpa [prefixWord, tailWord_6391683, baseEnd_6391683] using wordTrace_append hprefix tailTrace_6391683
  have hstable : (prefixWord ++ tailWord_6391683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6391683).length < 2 ^ (prefixWord ++ tailWord_6391683).sum := by decide
  have hdescent : baseEnd_6391683 < baseStart_6391683 := by decide
  rcases family_descends (prefixWord ++ tailWord_6391683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6391689 : List Nat := [1, 2, 1, 1, 5, 1, 1, 2, 1, 8]
def baseStart_6391689 : Nat := 118140960795 + 6391689 * 2 ^ 59
def prefixEnd_6391689 : Nat := 4983230072969 + 3 ^ 40 * 6391689 * 2
def baseEnd_6391689 : Nat := 1094002883685182740364221

theorem tailTrace_6391689 : CollatzResearch.WordTrace tailWord_6391689 prefixEnd_6391689 1094002883685182740364221 := by
  unfold tailWord_6391689
  simp only [CollatzResearch.WordTrace]
  refine ⟨233124049741009841418514121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155416033160673227612342747 233124049741009841418514121)
  ·
    refine ⟨174843037305757381063885591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233124049741009841418514121 174843037305757381063885591)
    ·
      refine ⟨262264555958636071595828387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174843037305757381063885591 262264555958636071595828387)
      ·
        refine ⟨393396833937954107393742581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262264555958636071595828387 393396833937954107393742581)
        ·
          refine ⟨36880953181683197568163367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 393396833937954107393742581 36880953181683197568163367)
          ·
            refine ⟨55321429772524796352245051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36880953181683197568163367 55321429772524796352245051)
            ·
              refine ⟨82982144658787194528367577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55321429772524796352245051 82982144658787194528367577)
              ·
                refine ⟨62236608494090395896275683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82982144658787194528367577 62236608494090395896275683)
                ·
                  refine ⟨93354912741135593844413525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62236608494090395896275683 93354912741135593844413525)
                  ·
                    refine ⟨1094002883685182740364221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 93354912741135593844413525 1094002883685182740364221)
                    ·
                      rfl

theorem cell23_6391689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 8].length) (baseStart_6391689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6391689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6391689 prefixEnd_6391689 := by exact prefixLift 6391689
  have htrace : WordTrace (prefixWord ++ tailWord_6391689) baseStart_6391689 baseEnd_6391689 := by
    simpa [prefixWord, tailWord_6391689, baseEnd_6391689] using wordTrace_append hprefix tailTrace_6391689
  have hstable : (prefixWord ++ tailWord_6391689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6391689).length < 2 ^ (prefixWord ++ tailWord_6391689).sum := by decide
  have hdescent : baseEnd_6391689 < baseStart_6391689 := by decide
  rcases family_descends (prefixWord ++ tailWord_6391689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6391694 : List Nat := [4, 1, 1, 5, 1, 2, 2, 1, 1, 2, 3]
def baseStart_6391694 : Nat := 118140960795 + 6391694 * 2 ^ 59
def prefixEnd_6391694 : Nat := 4983230072969 + 3 ^ 40 * 6391694 * 2
def baseEnd_6391694 : Nat := 3282011218458820701530141

theorem tailTrace_6391694 : CollatzResearch.WordTrace tailWord_6391694 prefixEnd_6391694 3282011218458820701530141 := by
  unfold tailWord_6391694
  simp only [CollatzResearch.WordTrace]
  refine ⟨29140529013248965909055767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155416154737327818181630757 29140529013248965909055767)
  ·
    refine ⟨43710793519873448863583651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29140529013248965909055767 43710793519873448863583651)
    ·
      refine ⟨65566190279810173295375477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43710793519873448863583651 65566190279810173295375477)
      ·
        refine ⟨6146830338732203746441451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65566190279810173295375477 6146830338732203746441451)
        ·
          refine ⟨9220245508098305619662177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6146830338732203746441451 9220245508098305619662177)
          ·
            refine ⟨6915184131073729214746633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9220245508098305619662177 6915184131073729214746633)
            ·
              refine ⟨5186388098305296911059975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6915184131073729214746633 5186388098305296911059975)
              ·
                refine ⟨7779582147457945366589963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5186388098305296911059975 7779582147457945366589963)
                ·
                  refine ⟨11669373221186918049884945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7779582147457945366589963 11669373221186918049884945)
                  ·
                    refine ⟨8752029915890188537413709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11669373221186918049884945 8752029915890188537413709)
                    ·
                      refine ⟨3282011218458820701530141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8752029915890188537413709 3282011218458820701530141)
                      ·
                        rfl

theorem cell23_6391694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_6391694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6391694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6391694 prefixEnd_6391694 := by exact prefixLift 6391694
  have htrace : WordTrace (prefixWord ++ tailWord_6391694) baseStart_6391694 baseEnd_6391694 := by
    simpa [prefixWord, tailWord_6391694, baseEnd_6391694] using wordTrace_append hprefix tailTrace_6391694
  have hstable : (prefixWord ++ tailWord_6391694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6391694).length < 2 ^ (prefixWord ++ tailWord_6391694).sum := by decide
  have hdescent : baseEnd_6391694 < baseStart_6391694 := by decide
  rcases family_descends (prefixWord ++ tailWord_6391694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6391699 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 6, 1, 5]
def baseStart_6391699 : Nat := 118140960795 + 6391699 * 2 ^ 59
def prefixEnd_6391699 : Nat := 4983230072969 + 3 ^ 40 * 6391699 * 2
def baseEnd_6391699 : Nat := 3282013785862093181967617

theorem tailTrace_6391699 : CollatzResearch.WordTrace tailWord_6391699 prefixEnd_6391699 3282013785862093181967617 := by
  unfold tailWord_6391699
  simp only [CollatzResearch.WordTrace]
  refine ⟨233124414470973613126378151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155416276313982408750918767 233124414470973613126378151)
  ·
    refine ⟨349686621706460419689567227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233124414470973613126378151 349686621706460419689567227)
    ·
      refine ⟨524529932559690629534350841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349686621706460419689567227 524529932559690629534350841)
      ·
        refine ⟨393397449419767972150763131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 524529932559690629534350841 393397449419767972150763131)
        ·
          refine ⟨590096174129651958226144697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 393397449419767972150763131 590096174129651958226144697)
          ·
            refine ⟨442572130597238968669608523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 590096174129651958226144697 442572130597238968669608523)
            ·
              refine ⟨663858195895858453004412785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 442572130597238968669608523 663858195895858453004412785)
              ·
                refine ⟨497893646921893839753309589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 663858195895858453004412785 497893646921893839753309589)
                ·
                  refine ⟨23338764699463773738436387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 497893646921893839753309589 23338764699463773738436387)
                  ·
                    refine ⟨35008147049195660607654581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23338764699463773738436387 35008147049195660607654581)
                    ·
                      refine ⟨3282013785862093181967617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35008147049195660607654581 3282013785862093181967617)
                      ·
                        rfl

theorem cell23_6391699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6, 1, 5].length) (baseStart_6391699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6391699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6391699 prefixEnd_6391699 := by exact prefixLift 6391699
  have htrace : WordTrace (prefixWord ++ tailWord_6391699) baseStart_6391699 baseEnd_6391699 := by
    simpa [prefixWord, tailWord_6391699, baseEnd_6391699] using wordTrace_append hprefix tailTrace_6391699
  have hstable : (prefixWord ++ tailWord_6391699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6391699).length < 2 ^ (prefixWord ++ tailWord_6391699).sum := by decide
  have hdescent : baseEnd_6391699 < baseStart_6391699 := by decide
  rcases family_descends (prefixWord ++ tailWord_6391699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6391706 : List Nat := [3, 1, 1, 4, 2, 1, 1, 2, 2, 6]
def baseStart_6391706 : Nat := 118140960795 + 6391706 * 2 ^ 59
def prefixEnd_6391706 : Nat := 4983230072969 + 3 ^ 40 * 6391706 * 2
def baseEnd_6391706 : Nat := 1094005793408891551526695

theorem tailTrace_6391706 : CollatzResearch.WordTrace tailWord_6391706 prefixEnd_6391706 1094005793408891551526695 := by
  unfold tailWord_6391706
  simp only [CollatzResearch.WordTrace]
  refine ⟨58281167445487063330470743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155416446521298835547921981 58281167445487063330470743)
  ·
    refine ⟨87421751168230594995706115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58281167445487063330470743 87421751168230594995706115)
    ·
      refine ⟨131132626752345892493559173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87421751168230594995706115 131132626752345892493559173)
      ·
        refine ⟨24587367516064854842542345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131132626752345892493559173 24587367516064854842542345)
        ·
          refine ⟨18440525637048641131906759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24587367516064854842542345 18440525637048641131906759)
          ·
            refine ⟨27660788455572961697860139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18440525637048641131906759 27660788455572961697860139)
            ·
              refine ⟨41491182683359442546790209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27660788455572961697860139 41491182683359442546790209)
              ·
                refine ⟨31118387012519581910092657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41491182683359442546790209 31118387012519581910092657)
                ·
                  refine ⟨23338790259389686432569493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31118387012519581910092657 23338790259389686432569493)
                  ·
                    refine ⟨1094005793408891551526695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23338790259389686432569493 1094005793408891551526695)
                    ·
                      rfl

theorem cell23_6391706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 2, 6].length) (baseStart_6391706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6391706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6391706 prefixEnd_6391706 := by exact prefixLift 6391706
  have htrace : WordTrace (prefixWord ++ tailWord_6391706) baseStart_6391706 baseEnd_6391706 := by
    simpa [prefixWord, tailWord_6391706, baseEnd_6391706] using wordTrace_append hprefix tailTrace_6391706
  have hstable : (prefixWord ++ tailWord_6391706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6391706).length < 2 ^ (prefixWord ++ tailWord_6391706).sum := by decide
  have hdescent : baseEnd_6391706 < baseStart_6391706 := by decide
  rcases family_descends (prefixWord ++ tailWord_6391706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6391730 : List Nat := [3, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2]
def baseStart_6391730 : Nat := 118140960795 + 6391730 * 2 ^ 59
def prefixEnd_6391730 : Nat := 4983230072969 + 3 ^ 40 * 6391730 * 2
def baseEnd_6391730 : Nat := 3282029703762382560679975

theorem tailTrace_6391730 : CollatzResearch.WordTrace tailWord_6391730 prefixEnd_6391730 3282029703762382560679975 := by
  unfold tailWord_6391730
  simp only [CollatzResearch.WordTrace]
  refine ⟨58281386283465326355189161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155417030089240870280504429 58281386283465326355189161)
  ·
    refine ⟨43711039712598994766391871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58281386283465326355189161 43711039712598994766391871)
    ·
      refine ⟨65566559568898492149587807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43711039712598994766391871 65566559568898492149587807)
      ·
        refine ⟨98349839353347738224381711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65566559568898492149587807 98349839353347738224381711)
        ·
          refine ⟨147524759030021607336572567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98349839353347738224381711 147524759030021607336572567)
          ·
            refine ⟨221287138545032411004858851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147524759030021607336572567 221287138545032411004858851)
            ·
              refine ⟨331930707817548616507288277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221287138545032411004858851 331930707817548616507288277)
              ·
                refine ⟨7779625964473795699389569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 331930707817548616507288277 7779625964473795699389569)
                ·
                  refine ⟨5834719473355346774542177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7779625964473795699389569 5834719473355346774542177)
                  ·
                    refine ⟨4376039605016510080906633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5834719473355346774542177 4376039605016510080906633)
                    ·
                      refine ⟨3282029703762382560679975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4376039605016510080906633 3282029703762382560679975)
                      ·
                        rfl

theorem cell23_6391730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2].length) (baseStart_6391730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6391730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6391730 prefixEnd_6391730 := by exact prefixLift 6391730
  have htrace : WordTrace (prefixWord ++ tailWord_6391730) baseStart_6391730 baseEnd_6391730 := by
    simpa [prefixWord, tailWord_6391730, baseEnd_6391730] using wordTrace_append hprefix tailTrace_6391730
  have hstable : (prefixWord ++ tailWord_6391730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6391730).length < 2 ^ (prefixWord ++ tailWord_6391730).sum := by decide
  have hdescent : baseEnd_6391730 < baseStart_6391730 := by decide
  rcases family_descends (prefixWord ++ tailWord_6391730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6391770 : List Nat := [3, 1, 1, 2, 6, 1, 1, 1, 7]
def baseStart_6391770 : Nat := 118140960795 + 6391770 * 2 ^ 59
def prefixEnd_6391770 : Nat := 4983230072969 + 3 ^ 40 * 6391770 * 2
def baseEnd_6391770 : Nat := 364672249220951378242199

theorem tailTrace_6391770 : CollatzResearch.WordTrace tailWord_6391770 prefixEnd_6391770 364672249220951378242199 := by
  unfold tailWord_6391770
  simp only [CollatzResearch.WordTrace]
  refine ⟨58281751013429098063053191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155418002702477594834808509 58281751013429098063053191)
  ·
    refine ⟨87422626520143647094579787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58281751013429098063053191 87422626520143647094579787)
    ·
      refine ⟨131133939780215470641869681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87422626520143647094579787 131133939780215470641869681)
      ·
        refine ⟨98350454835161602981402261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131133939780215470641869681 98350454835161602981402261)
        ·
          refine ⟨4610177570398200139753231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 98350454835161602981402261 4610177570398200139753231)
          ·
            refine ⟨6915266355597300209629847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4610177570398200139753231 6915266355597300209629847)
            ·
              refine ⟨10372899533395950314444771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6915266355597300209629847 10372899533395950314444771)
              ·
                refine ⟨15559349300093925471667157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10372899533395950314444771 15559349300093925471667157)
                ·
                  refine ⟨364672249220951378242199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15559349300093925471667157 364672249220951378242199)
                  ·
                    rfl

theorem cell23_6391770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 1, 7].length) (baseStart_6391770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6391770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6391770 prefixEnd_6391770 := by exact prefixLift 6391770
  have htrace : WordTrace (prefixWord ++ tailWord_6391770) baseStart_6391770 baseEnd_6391770 := by
    simpa [prefixWord, tailWord_6391770, baseEnd_6391770] using wordTrace_append hprefix tailTrace_6391770
  have hstable : (prefixWord ++ tailWord_6391770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6391770).length < 2 ^ (prefixWord ++ tailWord_6391770).sum := by decide
  have hdescent : baseEnd_6391770 < baseStart_6391770 := by decide
  rcases family_descends (prefixWord ++ tailWord_6391770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6391816 : List Nat := [2, 1, 3, 2, 1, 2, 2, 1, 2, 1, 6]
def baseStart_6391816 : Nat := 118140960795 + 6391816 * 2 ^ 59
def prefixEnd_6391816 : Nat := 4983230072969 + 3 ^ 40 * 6391816 * 2
def baseEnd_6391816 : Nat := 3282073863098669224204579

theorem tailTrace_6391816 : CollatzResearch.WordTrace tailWord_6391816 prefixEnd_6391816 3282073863098669224204579 := by
  unfold tailWord_6391816
  simp only [CollatzResearch.WordTrace]
  refine ⟨116564340905774871054193651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155419121207699828072258201 116564340905774871054193651)
  ·
    refine ⟨174846511358662306581290477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116564340905774871054193651 174846511358662306581290477)
    ·
      refine ⟨65567441759498364967983929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174846511358662306581290477 65567441759498364967983929)
      ·
        refine ⟨49175581319623773725987947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65567441759498364967983929 49175581319623773725987947)
        ·
          refine ⟨73763371979435660588981921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49175581319623773725987947 73763371979435660588981921)
          ·
            refine ⟨55322528984576745441736441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73763371979435660588981921 55322528984576745441736441)
            ·
              refine ⟨41491896738432559081302331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55322528984576745441736441 41491896738432559081302331)
              ·
                refine ⟨62237845107648838621953497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41491896738432559081302331 62237845107648838621953497)
                ·
                  refine ⟨46678383830736628966465123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62237845107648838621953497 46678383830736628966465123)
                  ·
                    refine ⟨70017575746104943449697685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46678383830736628966465123 70017575746104943449697685)
                    ·
                      refine ⟨3282073863098669224204579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70017575746104943449697685 3282073863098669224204579)
                      ·
                        rfl

theorem cell23_6391816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_6391816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6391816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6391816 prefixEnd_6391816 := by exact prefixLift 6391816
  have htrace : WordTrace (prefixWord ++ tailWord_6391816) baseStart_6391816 baseEnd_6391816 := by
    simpa [prefixWord, tailWord_6391816, baseEnd_6391816] using wordTrace_append hprefix tailTrace_6391816
  have hstable : (prefixWord ++ tailWord_6391816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6391816).length < 2 ^ (prefixWord ++ tailWord_6391816).sum := by decide
  have hdescent : baseEnd_6391816 < baseStart_6391816 := by decide
  rcases family_descends (prefixWord ++ tailWord_6391816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6391847 : List Nat := [1, 1, 7, 1, 2, 1, 1, 2, 3, 4]
def baseStart_6391847 : Nat := 118140960795 + 6391847 * 2 ^ 59
def prefixEnd_6391847 : Nat := 4983230072969 + 3 ^ 40 * 6391847 * 2
def baseEnd_6391847 : Nat := 1094029926999652867638979

theorem tailTrace_6391847 : CollatzResearch.WordTrace tailWord_6391847 prefixEnd_6391847 1094029926999652867638979 := by
  unfold tailWord_6391847
  simp only [CollatzResearch.WordTrace]
  refine ⟨233129812474437434402765795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155419874982958289601843863 233129812474437434402765795)
  ·
    refine ⟨349694718711656151604148693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233129812474437434402765795 349694718711656151604148693)
    ·
      refine ⟨8195969969804441053222235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 349694718711656151604148693 8195969969804441053222235)
      ·
        refine ⟨12293954954706661579833353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8195969969804441053222235 12293954954706661579833353)
        ·
          refine ⟨9220466216029996184875015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12293954954706661579833353 9220466216029996184875015)
          ·
            refine ⟨13830699324044994277312523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9220466216029996184875015 13830699324044994277312523)
            ·
              refine ⟨20746048986067491415968785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13830699324044994277312523 20746048986067491415968785)
              ·
                refine ⟨15559536739550618561976589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20746048986067491415968785 15559536739550618561976589)
                ·
                  refine ⟨5834826277331481960741221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15559536739550618561976589 5834826277331481960741221)
                  ·
                    refine ⟨1094029926999652867638979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5834826277331481960741221 1094029926999652867638979)
                    ·
                      rfl

theorem cell23_6391847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_6391847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6391847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6391847 prefixEnd_6391847 := by exact prefixLift 6391847
  have htrace : WordTrace (prefixWord ++ tailWord_6391847) baseStart_6391847 baseEnd_6391847 := by
    simpa [prefixWord, tailWord_6391847, baseEnd_6391847] using wordTrace_append hprefix tailTrace_6391847
  have hstable : (prefixWord ++ tailWord_6391847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6391847).length < 2 ^ (prefixWord ++ tailWord_6391847).sum := by decide
  have hdescent : baseEnd_6391847 < baseStart_6391847 := by decide
  rcases family_descends (prefixWord ++ tailWord_6391847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6391866 : List Nat := [3, 1, 1, 1, 3, 1, 1, 1, 2, 4, 5]
def baseStart_6391866 : Nat := 118140960795 + 6391866 * 2 ^ 59
def prefixEnd_6391866 : Nat := 4983230072969 + 3 ^ 40 * 6391866 * 2
def baseEnd_6391866 : Nat := 3282099537131394028579349

theorem tailTrace_6391866 : CollatzResearch.WordTrace tailWord_6391866 prefixEnd_6391866 3282099537131394028579349 := by
  unfold tailWord_6391866
  simp only [CollatzResearch.WordTrace]
  refine ⟨58282626365342150161926863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155420336974245733765138301 58282626365342150161926863)
  ·
    refine ⟨87423939548013225242890295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58282626365342150161926863 87423939548013225242890295)
    ·
      refine ⟨131135909322019837864335443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87423939548013225242890295 131135909322019837864335443)
      ·
        refine ⟨196703863983029756796503165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131135909322019837864335443 196703863983029756796503165)
        ·
          refine ⟨73763948993636158798688687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196703863983029756796503165 73763948993636158798688687)
          ·
            refine ⟨110645923490454238198033031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73763948993636158798688687 110645923490454238198033031)
            ·
              refine ⟨165968885235681357297049547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110645923490454238198033031 165968885235681357297049547)
              ·
                refine ⟨248953327853522035945574321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165968885235681357297049547 248953327853522035945574321)
                ·
                  refine ⟨186714995890141526959180741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 248953327853522035945574321 186714995890141526959180741)
                  ·
                    refine ⟨35009061729401536304846389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 186714995890141526959180741 35009061729401536304846389)
                    ·
                      refine ⟨3282099537131394028579349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35009061729401536304846389 3282099537131394028579349)
                      ·
                        rfl

theorem cell23_6391866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 2, 4, 5].length) (baseStart_6391866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6391866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6391866 prefixEnd_6391866 := by exact prefixLift 6391866
  have htrace : WordTrace (prefixWord ++ tailWord_6391866) baseStart_6391866 baseEnd_6391866 := by
    simpa [prefixWord, tailWord_6391866, baseEnd_6391866] using wordTrace_append hprefix tailTrace_6391866
  have hstable : (prefixWord ++ tailWord_6391866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6391866).length < 2 ^ (prefixWord ++ tailWord_6391866).sum := by decide
  have hdescent : baseEnd_6391866 < baseStart_6391866 := by decide
  rcases family_descends (prefixWord ++ tailWord_6391866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6391894 : List Nat := [5, 2, 2, 1, 1, 2, 3, 1, 6]
def baseStart_6391894 : Nat := 118140960795 + 6391894 * 2 ^ 59
def prefixEnd_6391894 : Nat := 4983230072969 + 3 ^ 40 * 6391894 * 2
def baseEnd_6391894 : Nat := 364679323843302213225469

theorem tailTrace_6391894 : CollatzResearch.WordTrace tailWord_6391894 prefixEnd_6391894 364679323843302213225469 := by
  unfold tailWord_6391894
  simp only [CollatzResearch.WordTrace]
  refine ⟨14570720419079197589357921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 155421017803511440953151157 14570720419079197589357921)
  ·
    refine ⟨10928040314309398192018441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14570720419079197589357921 10928040314309398192018441)
    ·
      refine ⟨8196030235732048644013831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10928040314309398192018441 8196030235732048644013831)
      ·
        refine ⟨12294045353598072966020747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8196030235732048644013831 12294045353598072966020747)
        ·
          refine ⟨18441068030397109449031121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12294045353598072966020747 18441068030397109449031121)
          ·
            refine ⟨13830801022797832086773341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18441068030397109449031121 13830801022797832086773341)
            ·
              refine ⟨5186550383549187032540003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13830801022797832086773341 5186550383549187032540003)
              ·
                refine ⟨7779825575323780548810005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5186550383549187032540003 7779825575323780548810005)
                ·
                  refine ⟨364679323843302213225469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7779825575323780548810005 364679323843302213225469)
                  ·
                    rfl

theorem cell23_6391894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_6391894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6391894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6391894 prefixEnd_6391894 := by exact prefixLift 6391894
  have htrace : WordTrace (prefixWord ++ tailWord_6391894) baseStart_6391894 baseEnd_6391894 := by
    simpa [prefixWord, tailWord_6391894, baseEnd_6391894] using wordTrace_append hprefix tailTrace_6391894
  have hstable : (prefixWord ++ tailWord_6391894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6391894).length < 2 ^ (prefixWord ++ tailWord_6391894).sum := by decide
  have hdescent : baseEnd_6391894 < baseStart_6391894 := by decide
  rcases family_descends (prefixWord ++ tailWord_6391894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6391933 : List Nat := [1, 4, 1, 1, 3, 4, 9]
def baseStart_6391933 : Nat := 118140960795 + 6391933 * 2 ^ 59
def prefixEnd_6391933 : Nat := 4983230072969 + 3 ^ 40 * 6391933 * 2
def baseEnd_6391933 : Nat := 40520172102904262548661

theorem tailTrace_6391933 : CollatzResearch.WordTrace tailWord_6391933 prefixEnd_6391933 40520172102904262548661 := by
  unfold tailWord_6391933
  simp only [CollatzResearch.WordTrace]
  refine ⟨233132949152125871090396453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155421966101417247393597635 233132949152125871090396453)
  ·
    refine ⟨43712427966023600829449335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 233132949152125871090396453 43712427966023600829449335)
    ·
      refine ⟨65568641949035401244174003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43712427966023600829449335 65568641949035401244174003)
      ·
        refine ⟨98352962923553101866261005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65568641949035401244174003 98352962923553101866261005)
        ·
          refine ⟨36882361096332413199847877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98352962923553101866261005 36882361096332413199847877)
          ·
            refine ⟨6915442705562327474971477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36882361096332413199847877 6915442705562327474971477)
            ·
              refine ⟨40520172102904262548661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6915442705562327474971477 40520172102904262548661)
              ·
                rfl

theorem cell23_6391933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 9].length) (baseStart_6391933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6391933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6391933 prefixEnd_6391933 := by exact prefixLift 6391933
  have htrace : WordTrace (prefixWord ++ tailWord_6391933) baseStart_6391933 baseEnd_6391933 := by
    simpa [prefixWord, tailWord_6391933, baseEnd_6391933] using wordTrace_append hprefix tailTrace_6391933
  have hstable : (prefixWord ++ tailWord_6391933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6391933).length < 2 ^ (prefixWord ++ tailWord_6391933).sum := by decide
  have hdescent : baseEnd_6391933 < baseStart_6391933 := by decide
  rcases family_descends (prefixWord ++ tailWord_6391933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6391944 : List Nat := [2, 1, 3, 4, 1, 1, 3, 1, 3, 2, 2]
def baseStart_6391944 : Nat := 118140960795 + 6391944 * 2 ^ 59
def prefixEnd_6391944 : Nat := 4983230072969 + 3 ^ 40 * 6391944 * 2
def baseEnd_6391944 : Nat := 3282139588622444723403991

theorem tailTrace_6391944 : CollatzResearch.WordTrace tailWord_6391944 prefixEnd_6391944 3282139588622444723403991 := by
  unfold tailWord_6391944
  simp only [CollatzResearch.WordTrace]
  refine ⟨116566675177543009984523443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155422233570057346646031257 116566675177543009984523443)
  ·
    refine ⟨174850012766314514976785165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116566675177543009984523443 174850012766314514976785165)
    ·
      refine ⟨65568754787367943116294437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174850012766314514976785165 65568754787367943116294437)
      ·
        refine ⟨12294141522631489334305207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65568754787367943116294437 12294141522631489334305207)
        ·
          refine ⟨18441212283947234001457811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12294141522631489334305207 18441212283947234001457811)
          ·
            refine ⟨27661818425920851002186717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18441212283947234001457811 27661818425920851002186717)
            ·
              refine ⟨10373181909720319125820019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27661818425920851002186717 10373181909720319125820019)
              ·
                refine ⟨15559772864580478688730029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10373181909720319125820019 15559772864580478688730029)
                ·
                  refine ⟨5834914824217679508273761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15559772864580478688730029 5834914824217679508273761)
                  ·
                    refine ⟨4376186118163259631205321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5834914824217679508273761 4376186118163259631205321)
                    ·
                      refine ⟨3282139588622444723403991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4376186118163259631205321 3282139588622444723403991)
                      ·
                        rfl

theorem cell23_6391944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_6391944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6391944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6391944 prefixEnd_6391944 := by exact prefixLift 6391944
  have htrace : WordTrace (prefixWord ++ tailWord_6391944) baseStart_6391944 baseEnd_6391944 := by
    simpa [prefixWord, tailWord_6391944, baseEnd_6391944] using wordTrace_append hprefix tailTrace_6391944
  have hstable : (prefixWord ++ tailWord_6391944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6391944).length < 2 ^ (prefixWord ++ tailWord_6391944).sum := by decide
  have hdescent : baseEnd_6391944 < baseStart_6391944 := by decide
  rcases family_descends (prefixWord ++ tailWord_6391944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6391950 : List Nat := [4, 1, 1, 3, 3, 1, 2, 8]
def baseStart_6391950 : Nat := 118140960795 + 6391950 * 2 ^ 59
def prefixEnd_6391950 : Nat := 4983230072969 + 3 ^ 40 * 6391950 * 2
def baseEnd_6391950 : Nat := 121560839611347099997369

theorem tailTrace_6391950 : CollatzResearch.WordTrace tailWord_6391950 prefixEnd_6391950 121560839611347099997369 := by
  unfold tailWord_6391950
  simp only [CollatzResearch.WordTrace]
  refine ⟨29141696149133035374220663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155422379462042855329176869 29141696149133035374220663)
  ·
    refine ⟨43712544223699553061330995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29141696149133035374220663 43712544223699553061330995)
    ·
      refine ⟨65568816335549329591996493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43712544223699553061330995 65568816335549329591996493)
      ·
        refine ⟨24588306125830998596998685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65568816335549329591996493 24588306125830998596998685)
        ·
          refine ⟨9220614797186624473874507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24588306125830998596998685 9220614797186624473874507)
          ·
            refine ⟨13830922195779936710811761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9220614797186624473874507 13830922195779936710811761)
            ·
              refine ⟨10373191646834952533108821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13830922195779936710811761 10373191646834952533108821)
              ·
                refine ⟨121560839611347099997369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10373191646834952533108821 121560839611347099997369)
                ·
                  rfl

theorem cell23_6391950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 8].length) (baseStart_6391950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6391950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6391950 prefixEnd_6391950 := by exact prefixLift 6391950
  have htrace : WordTrace (prefixWord ++ tailWord_6391950) baseStart_6391950 baseEnd_6391950 := by
    simpa [prefixWord, tailWord_6391950, baseEnd_6391950] using wordTrace_append hprefix tailTrace_6391950
  have hstable : (prefixWord ++ tailWord_6391950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6391950).length < 2 ^ (prefixWord ++ tailWord_6391950).sum := by decide
  have hdescent : baseEnd_6391950 < baseStart_6391950 := by decide
  rcases family_descends (prefixWord ++ tailWord_6391950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6391988 : List Nat := [2, 5, 3, 1, 1, 1, 2, 2, 2, 4]
def baseStart_6391988 : Nat := 118140960795 + 6391988 * 2 ^ 59
def prefixEnd_6391988 : Nat := 4983230072969 + 3 ^ 40 * 6391988 * 2
def baseEnd_6391988 : Nat := 1094054060590414183751263

theorem tailTrace_6391988 : CollatzResearch.WordTrace tailWord_6391988 prefixEnd_6391988 1094054060590414183751263 := by
  unfold tailWord_6391988
  simp only [CollatzResearch.WordTrace]
  refine ⟨116567477583463307741824309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155423303444617743655765745 116567477583463307741824309)
  ·
    refine ⟨10928201023449685100796029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 116567477583463307741824309 10928201023449685100796029)
    ·
      refine ⟨4098075383793631912798511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10928201023449685100796029 4098075383793631912798511)
      ·
        refine ⟨6147113075690447869197767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4098075383793631912798511 6147113075690447869197767)
        ·
          refine ⟨9220669613535671803796651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6147113075690447869197767 9220669613535671803796651)
          ·
            refine ⟨13831004420303507705694977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9220669613535671803796651 13831004420303507705694977)
            ·
              refine ⟨10373253315227630779271233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13831004420303507705694977 10373253315227630779271233)
              ·
                refine ⟨7779939986420723084453425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10373253315227630779271233 7779939986420723084453425)
                ·
                  refine ⟨5834954989815542313340069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7779939986420723084453425 5834954989815542313340069)
                  ·
                    refine ⟨1094054060590414183751263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5834954989815542313340069 1094054060590414183751263)
                    ·
                      rfl

theorem cell23_6391988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_6391988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6391988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6391988 prefixEnd_6391988 := by exact prefixLift 6391988
  have htrace : WordTrace (prefixWord ++ tailWord_6391988) baseStart_6391988 baseEnd_6391988 := by
    simpa [prefixWord, tailWord_6391988, baseEnd_6391988] using wordTrace_append hprefix tailTrace_6391988
  have hstable : (prefixWord ++ tailWord_6391988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6391988).length < 2 ^ (prefixWord ++ tailWord_6391988).sum := by decide
  have hdescent : baseEnd_6391988 < baseStart_6391988 := by decide
  rcases family_descends (prefixWord ++ tailWord_6391988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6391993 : List Nat := [1, 2, 1, 4, 1, 2, 2, 2, 2, 6]
def baseStart_6391993 : Nat := 118140960795 + 6391993 * 2 ^ 59
def prefixEnd_6391993 : Nat := 4983230072969 + 3 ^ 40 * 6391993 * 2
def baseEnd_6391993 : Nat := 1094054916391505010563755

theorem tailTrace_6391993 : CollatzResearch.WordTrace tailWord_6391993 prefixEnd_6391993 1094054916391505010563755 := by
  unfold tailWord_6391993
  simp only [CollatzResearch.WordTrace]
  refine ⟨233135137531908501337580633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155423425021272334225053755 233135137531908501337580633)
  ·
    refine ⟨174851353148931376003185475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233135137531908501337580633 174851353148931376003185475)
    ·
      refine ⟨262277029723397064004778213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174851353148931376003185475 262277029723397064004778213)
      ·
        refine ⟨49176943073136949500895915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 262277029723397064004778213 49176943073136949500895915)
        ·
          refine ⟨73765414609705424251343873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49176943073136949500895915 73765414609705424251343873)
          ·
            refine ⟨55324060957279068188507905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73765414609705424251343873 55324060957279068188507905)
            ·
              refine ⟨41493045717959301141380929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55324060957279068188507905 41493045717959301141380929)
              ·
                refine ⟨31119784288469475856035697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41493045717959301141380929 31119784288469475856035697)
                ·
                  refine ⟨23339838216352106892026773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31119784288469475856035697 23339838216352106892026773)
                  ·
                    refine ⟨1094054916391505010563755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23339838216352106892026773 1094054916391505010563755)
                    ·
                      rfl

theorem cell23_6391993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 2, 6].length) (baseStart_6391993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6391993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6391993 prefixEnd_6391993 := by exact prefixLift 6391993
  have htrace : WordTrace (prefixWord ++ tailWord_6391993) baseStart_6391993 baseEnd_6391993 := by
    simpa [prefixWord, tailWord_6391993, baseEnd_6391993] using wordTrace_append hprefix tailTrace_6391993
  have hstable : (prefixWord ++ tailWord_6391993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6391993).length < 2 ^ (prefixWord ++ tailWord_6391993).sum := by decide
  have hdescent : baseEnd_6391993 < baseStart_6391993 := by decide
  rcases family_descends (prefixWord ++ tailWord_6391993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6392063 : List Nat := [1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 7]
def baseStart_6392063 : Nat := 118140960795 + 6392063 * 2 ^ 59
def prefixEnd_6392063 : Nat := 4983230072969 + 3 ^ 40 * 6392063 * 2
def baseEnd_6392063 : Nat := 3282200692820329757815943

theorem tailTrace_6392063 : CollatzResearch.WordTrace tailWord_6392063 prefixEnd_6392063 3282200692820329757815943 := by
  unfold tailWord_6392063
  simp only [CollatzResearch.WordTrace]
  refine ⟨233137690641654903292628843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155425127094436602195085895 233137690641654903292628843)
  ·
    refine ⟨349706535962482354938943265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233137690641654903292628843 349706535962482354938943265)
    ·
      refine ⟨262279901971861766204207449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 349706535962482354938943265 262279901971861766204207449)
      ·
        refine ⟨196709926478896324653155587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262279901971861766204207449 196709926478896324653155587)
        ·
          refine ⟨295064889718344486979733381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196709926478896324653155587 295064889718344486979733381)
          ·
            refine ⟨55324666822189591308700009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 295064889718344486979733381 55324666822189591308700009)
            ·
              refine ⟨41493500116642193481525007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55324666822189591308700009 41493500116642193481525007)
              ·
                refine ⟨62240250174963290222287511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41493500116642193481525007 62240250174963290222287511)
                ·
                  refine ⟨93360375262444935333431267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62240250174963290222287511 93360375262444935333431267)
                  ·
                    refine ⟨140040562893667403000146901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 93360375262444935333431267 140040562893667403000146901)
                    ·
                      refine ⟨3282200692820329757815943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 140040562893667403000146901 3282200692820329757815943)
                      ·
                        rfl

theorem cell23_6392063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 7].length) (baseStart_6392063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6392063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6392063 prefixEnd_6392063 := by exact prefixLift 6392063
  have htrace : WordTrace (prefixWord ++ tailWord_6392063) baseStart_6392063 baseEnd_6392063 := by
    simpa [prefixWord, tailWord_6392063, baseEnd_6392063] using wordTrace_append hprefix tailTrace_6392063
  have hstable : (prefixWord ++ tailWord_6392063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6392063).length < 2 ^ (prefixWord ++ tailWord_6392063).sum := by decide
  have hdescent : baseEnd_6392063 < baseStart_6392063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6392063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6392068 : List Nat := [2, 3, 2, 2, 3, 1, 3, 1, 2, 2, 2]
def baseStart_6392068 : Nat := 118140960795 + 6392068 * 2 ^ 59
def prefixEnd_6392068 : Nat := 4983230072969 + 3 ^ 40 * 6392068 * 2
def baseEnd_6392068 : Nat := 3282203260223602238253421

theorem tailTrace_6392068 : CollatzResearch.WordTrace tailWord_6392068 prefixEnd_6392068 3282203260223602238253421 := by
  unfold tailWord_6392068
  simp only [CollatzResearch.WordTrace]
  refine ⟨116568936503318394573280429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155425248671091192764373905 116568936503318394573280429)
  ·
    refine ⟨43713351188744397964980161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116568936503318394573280429 43713351188744397964980161)
    ·
      refine ⟨32785013391558298473735121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43713351188744397964980161 32785013391558298473735121)
      ·
        refine ⟨24588760043668723855301341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32785013391558298473735121 24588760043668723855301341)
        ·
          refine ⟨9220785016375771445738003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24588760043668723855301341 9220785016375771445738003)
          ·
            refine ⟨13831177524563657168607005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9220785016375771445738003 13831177524563657168607005)
            ·
              refine ⟨5186691571711371438227627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13831177524563657168607005 5186691571711371438227627)
              ·
                refine ⟨7780037357567057157341441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5186691571711371438227627 7780037357567057157341441)
                ·
                  refine ⟨5835028018175292868006081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7780037357567057157341441 5835028018175292868006081)
                  ·
                    refine ⟨4376271013631469651004561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5835028018175292868006081 4376271013631469651004561)
                    ·
                      refine ⟨3282203260223602238253421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4376271013631469651004561 3282203260223602238253421)
                      ·
                        rfl

theorem cell23_6392068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_6392068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6392068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6392068 prefixEnd_6392068 := by exact prefixLift 6392068
  have htrace : WordTrace (prefixWord ++ tailWord_6392068) baseStart_6392068 baseEnd_6392068 := by
    simpa [prefixWord, tailWord_6392068, baseEnd_6392068] using wordTrace_append hprefix tailTrace_6392068
  have hstable : (prefixWord ++ tailWord_6392068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6392068).length < 2 ^ (prefixWord ++ tailWord_6392068).sum := by decide
  have hdescent : baseEnd_6392068 < baseStart_6392068 := by decide
  rcases family_descends (prefixWord ++ tailWord_6392068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6392168 : List Nat := [2, 1, 4, 2, 2, 3, 2, 2, 1, 4]
def baseStart_6392168 : Nat := 118140960795 + 6392168 * 2 ^ 59
def prefixEnd_6392168 : Nat := 4983230072969 + 3 ^ 40 * 6392168 * 2
def baseEnd_6392168 : Nat := 1094084869429683949000987

theorem tailTrace_6392168 : CollatzResearch.WordTrace tailWord_6392168 prefixEnd_6392168 1094084869429683949000987 := by
  unfold tailWord_6392168
  simp only [CollatzResearch.WordTrace]
  refine ⟨116570760153137253112600579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155427680204183004150134105 116570760153137253112600579)
  ·
    refine ⟨174856140229705879668900869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116570760153137253112600579 174856140229705879668900869)
    ·
      refine ⟨32785526293069852437918913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 174856140229705879668900869 32785526293069852437918913)
      ·
        refine ⟨24589144719802389328439185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32785526293069852437918913 24589144719802389328439185)
        ·
          refine ⟨18441858539851791996329389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24589144719802389328439185 18441858539851791996329389)
          ·
            refine ⟨6915696952444421998623521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18441858539851791996329389 6915696952444421998623521)
            ·
              refine ⟨5186772714333316498967641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6915696952444421998623521 5186772714333316498967641)
              ·
                refine ⟨3890079535749987374225731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5186772714333316498967641 3890079535749987374225731)
                ·
                  refine ⟨5835119303624981061338597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3890079535749987374225731 5835119303624981061338597)
                  ·
                    refine ⟨1094084869429683949000987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5835119303624981061338597 1094084869429683949000987)
                    ·
                      rfl

theorem cell23_6392168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2, 2, 1, 4].length) (baseStart_6392168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6392168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6392168 prefixEnd_6392168 := by exact prefixLift 6392168
  have htrace : WordTrace (prefixWord ++ tailWord_6392168) baseStart_6392168 baseEnd_6392168 := by
    simpa [prefixWord, tailWord_6392168, baseEnd_6392168] using wordTrace_append hprefix tailTrace_6392168
  have hstable : (prefixWord ++ tailWord_6392168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6392168).length < 2 ^ (prefixWord ++ tailWord_6392168).sum := by decide
  have hdescent : baseEnd_6392168 < baseStart_6392168 := by decide
  rcases family_descends (prefixWord ++ tailWord_6392168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6392197 : List Nat := [1, 3, 1, 1, 3, 1, 1, 6, 1, 1, 4]
def baseStart_6392197 : Nat := 118140960795 + 6392197 * 2 ^ 59
def prefixEnd_6392197 : Nat := 4983230072969 + 3 ^ 40 * 6392197 * 2
def baseEnd_6392197 : Nat := 3282269499228032233540327

theorem tailTrace_6392197 : CollatzResearch.WordTrace tailWord_6392197 prefixEnd_6392197 3282269499228032233540327 := by
  unfold tailWord_6392197
  simp only [CollatzResearch.WordTrace]
  refine ⟨233142578023169444178006845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155428385348779629452004563 233142578023169444178006845)
  ·
    refine ⟨87428466758688541566752567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233142578023169444178006845 87428466758688541566752567)
    ·
      refine ⟨131142700138032812350128851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87428466758688541566752567 131142700138032812350128851)
      ·
        refine ⟨196714050207049218525193277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131142700138032812350128851 196714050207049218525193277)
        ·
          refine ⟨73767768827643456946947479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196714050207049218525193277 73767768827643456946947479)
          ·
            refine ⟨110651653241465185420421219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73767768827643456946947479 110651653241465185420421219)
            ·
              refine ⟨165977479862197778130631829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110651653241465185420421219 165977479862197778130631829)
              ·
                refine ⟨7780194368540520849873367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 165977479862197778130631829 7780194368540520849873367)
                ·
                  refine ⟨11670291552810781274810051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7780194368540520849873367 11670291552810781274810051)
                  ·
                    refine ⟨17505437329216171912215077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11670291552810781274810051 17505437329216171912215077)
                    ·
                      refine ⟨3282269499228032233540327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17505437329216171912215077 3282269499228032233540327)
                      ·
                        rfl

theorem cell23_6392197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 6, 1, 1, 4].length) (baseStart_6392197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6392197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6392197 prefixEnd_6392197 := by exact prefixLift 6392197
  have htrace : WordTrace (prefixWord ++ tailWord_6392197) baseStart_6392197 baseEnd_6392197 := by
    simpa [prefixWord, tailWord_6392197, baseEnd_6392197] using wordTrace_append hprefix tailTrace_6392197
  have hstable : (prefixWord ++ tailWord_6392197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6392197).length < 2 ^ (prefixWord ++ tailWord_6392197).sum := by decide
  have hdescent : baseEnd_6392197 < baseStart_6392197 := by decide
  rcases family_descends (prefixWord ++ tailWord_6392197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6392201 : List Nat := [1, 2, 1, 1, 6, 3, 1, 1, 2, 3, 2]
def baseStart_6392201 : Nat := 118140960795 + 6392201 * 2 ^ 59
def prefixEnd_6392201 : Nat := 4983230072969 + 3 ^ 40 * 6392201 * 2
def baseEnd_6392201 : Nat := 3282271553150650217890309

theorem tailTrace_6392201 : CollatzResearch.WordTrace tailWord_6392201 prefixEnd_6392201 3282271553150650217890309 := by
  unfold tailWord_6392201
  simp only [CollatzResearch.WordTrace]
  refine ⟨233142723915154952861152457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155428482610103301907434971 233142723915154952861152457)
  ·
    refine ⟨174857042936366214645864343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233142723915154952861152457 174857042936366214645864343)
    ·
      refine ⟨262285564404549321968796515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174857042936366214645864343 262285564404549321968796515)
      ·
        refine ⟨393428346606823982953194773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262285564404549321968796515 393428346606823982953194773)
        ·
          refine ⟨18441953747194874200931005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 393428346606823982953194773 18441953747194874200931005)
          ·
            refine ⟨6915732655198077825349127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18441953747194874200931005 6915732655198077825349127)
            ·
              refine ⟨10373598982797116738023691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6915732655198077825349127 10373598982797116738023691)
              ·
                refine ⟨15560398474195675107035537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10373598982797116738023691 15560398474195675107035537)
                ·
                  refine ⟨11670298855646756330276653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15560398474195675107035537 11670298855646756330276653)
                  ·
                    refine ⟨4376362070867533623853745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11670298855646756330276653 4376362070867533623853745)
                    ·
                      refine ⟨3282271553150650217890309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4376362070867533623853745 3282271553150650217890309)
                      ·
                        rfl

theorem cell23_6392201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 1, 2, 3, 2].length) (baseStart_6392201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6392201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6392201 prefixEnd_6392201 := by exact prefixLift 6392201
  have htrace : WordTrace (prefixWord ++ tailWord_6392201) baseStart_6392201 baseEnd_6392201 := by
    simpa [prefixWord, tailWord_6392201, baseEnd_6392201] using wordTrace_append hprefix tailTrace_6392201
  have hstable : (prefixWord ++ tailWord_6392201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6392201).length < 2 ^ (prefixWord ++ tailWord_6392201).sum := by decide
  have hdescent : baseEnd_6392201 < baseStart_6392201 := by decide
  rcases family_descends (prefixWord ++ tailWord_6392201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6392224 : List Nat := [2, 1, 1, 4, 1, 3, 3, 2, 2, 4]
def baseStart_6392224 : Nat := 118140960795 + 6392224 * 2 ^ 59
def prefixEnd_6392224 : Nat := 4983230072969 + 3 ^ 40 * 6392224 * 2
def baseEnd_6392224 : Nat := 1094094454401901209300901

theorem tailTrace_6392224 : CollatzResearch.WordTrace tailWord_6392224 prefixEnd_6392224 1094094454401901209300901 := by
  unfold tailWord_6392224
  simp only [CollatzResearch.WordTrace]
  refine ⟨116571781397035813894619863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155429041862714418526159817 116571781397035813894619863)
  ·
    refine ⟨174857672095553720841929795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116571781397035813894619863 174857672095553720841929795)
    ·
      refine ⟨262286508143330581262894693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174857672095553720841929795 262286508143330581262894693)
      ·
        refine ⟨49178720276874483986792755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 262286508143330581262894693 49178720276874483986792755)
        ·
          refine ⟨73768080415311725980189133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49178720276874483986792755 73768080415311725980189133)
          ·
            refine ⟨27663030155741897242570925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73768080415311725980189133 27663030155741897242570925)
            ·
              refine ⟨10373636308403211465964097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27663030155741897242570925 10373636308403211465964097)
              ·
                refine ⟨7780227231302408599473073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10373636308403211465964097 7780227231302408599473073)
                ·
                  refine ⟨5835170423476806449604805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7780227231302408599473073 5835170423476806449604805)
                  ·
                    refine ⟨1094094454401901209300901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5835170423476806449604805 1094094454401901209300901)
                    ·
                      rfl

theorem cell23_6392224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 2, 2, 4].length) (baseStart_6392224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6392224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6392224 prefixEnd_6392224 := by exact prefixLift 6392224
  have htrace : WordTrace (prefixWord ++ tailWord_6392224) baseStart_6392224 baseEnd_6392224 := by
    simpa [prefixWord, tailWord_6392224, baseEnd_6392224] using wordTrace_append hprefix tailTrace_6392224
  have hstable : (prefixWord ++ tailWord_6392224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6392224).length < 2 ^ (prefixWord ++ tailWord_6392224).sum := by decide
  have hdescent : baseEnd_6392224 < baseStart_6392224 := by decide
  rcases family_descends (prefixWord ++ tailWord_6392224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6392231 : List Nat := [1, 1, 6, 1, 1, 2, 1, 3, 3, 2, 2]
def baseStart_6392231 : Nat := 118140960795 + 6392231 * 2 ^ 59
def prefixEnd_6392231 : Nat := 4983230072969 + 3 ^ 40 * 6392231 * 2
def baseEnd_6392231 : Nat := 3282286957570285100515171

theorem tailTrace_6392231 : CollatzResearch.WordTrace tailWord_6392231 prefixEnd_6392231 3282286957570285100515171 := by
  unfold tailWord_6392231
  simp only [CollatzResearch.WordTrace]
  refine ⟨233143818105046267984744547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155429212070030845323163031 233143818105046267984744547)
  ·
    refine ⟨349715727157569401977116821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233143818105046267984744547 349715727157569401977116821)
    ·
      refine ⟨16392924710511065717677351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 349715727157569401977116821 16392924710511065717677351)
      ·
        refine ⟨24589387065766598576516027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16392924710511065717677351 24589387065766598576516027)
        ·
          refine ⟨36884080598649897864774041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24589387065766598576516027 36884080598649897864774041)
          ·
            refine ⟨27663060448987423398580531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36884080598649897864774041 27663060448987423398580531)
            ·
              refine ⟨41494590673481135097870797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27663060448987423398580531 41494590673481135097870797)
              ·
                refine ⟨15560471502555425661701549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41494590673481135097870797 15560471502555425661701549)
                ·
                  refine ⟨5835176813458284623138081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15560471502555425661701549 5835176813458284623138081)
                  ·
                    refine ⟨4376382610093713467353561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5835176813458284623138081 4376382610093713467353561)
                    ·
                      refine ⟨3282286957570285100515171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4376382610093713467353561 3282286957570285100515171)
                      ·
                        rfl

theorem cell23_6392231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_6392231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6392231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6392231 prefixEnd_6392231 := by exact prefixLift 6392231
  have htrace : WordTrace (prefixWord ++ tailWord_6392231) baseStart_6392231 baseEnd_6392231 := by
    simpa [prefixWord, tailWord_6392231, baseEnd_6392231] using wordTrace_append hprefix tailTrace_6392231
  have hstable : (prefixWord ++ tailWord_6392231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6392231).length < 2 ^ (prefixWord ++ tailWord_6392231).sum := by decide
  have hdescent : baseEnd_6392231 < baseStart_6392231 := by decide
  rcases family_descends (prefixWord ++ tailWord_6392231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6392241 : List Nat := [1, 2, 2, 4, 1, 3, 3, 1, 2, 4]
def baseStart_6392241 : Nat := 118140960795 + 6392241 * 2 ^ 59
def prefixEnd_6392241 : Nat := 4983230072969 + 3 ^ 40 * 6392241 * 2
def baseEnd_6392241 : Nat := 1094097364125610020463375

theorem tailTrace_6392241 : CollatzResearch.WordTrace tailWord_6392241 prefixEnd_6392241 1094097364125610020463375 := by
  unfold tailWord_6392241
  simp only [CollatzResearch.WordTrace]
  refine ⟨233144182835010039692608577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155429455223340026461739051 233144182835010039692608577)
  ·
    refine ⟨174858137126257529769456433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233144182835010039692608577 174858137126257529769456433)
    ·
      refine ⟨131143602844693147327092325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174858137126257529769456433 131143602844693147327092325)
      ·
        refine ⟨24589425533379965123829811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131143602844693147327092325 24589425533379965123829811)
        ·
          refine ⟨36884138300069947685744717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24589425533379965123829811 36884138300069947685744717)
          ·
            refine ⟨13831551862526230382154269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36884138300069947685744717 13831551862526230382154269)
            ·
              refine ⟨5186831948447336393307851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13831551862526230382154269 5186831948447336393307851)
              ·
                refine ⟨7780247922671004589961777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5186831948447336393307851 7780247922671004589961777)
                ·
                  refine ⟨5835185942003253442471333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7780247922671004589961777 5835185942003253442471333)
                  ·
                    refine ⟨1094097364125610020463375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5835185942003253442471333 1094097364125610020463375)
                    ·
                      rfl

theorem cell23_6392241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3, 1, 2, 4].length) (baseStart_6392241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6392241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6392241 prefixEnd_6392241 := by exact prefixLift 6392241
  have htrace : WordTrace (prefixWord ++ tailWord_6392241) baseStart_6392241 baseEnd_6392241 := by
    simpa [prefixWord, tailWord_6392241, baseEnd_6392241] using wordTrace_append hprefix tailTrace_6392241
  have hstable : (prefixWord ++ tailWord_6392241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6392241).length < 2 ^ (prefixWord ++ tailWord_6392241).sum := by decide
  have hdescent : baseEnd_6392241 < baseStart_6392241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6392241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6392250 : List Nat := [3, 1, 1, 1, 2, 1, 1, 4, 2, 7]
def baseStart_6392250 : Nat := 118140960795 + 6392250 * 2 ^ 59
def prefixEnd_6392250 : Nat := 4983230072969 + 3 ^ 40 * 6392250 * 2
def baseEnd_6392250 : Nat := 1094098904567573508725861

theorem tailTrace_6392250 : CollatzResearch.WordTrace tailWord_6392250 prefixEnd_6392250 1094098904567573508725861 := by
  unfold tailWord_6392250
  simp only [CollatzResearch.WordTrace]
  refine ⟨58286127772994358557421551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155429674061318289486457469 58286127772994358557421551)
  ·
    refine ⟨87429191659491537836132327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58286127772994358557421551 87429191659491537836132327)
    ·
      refine ⟨131143787489237306754198491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87429191659491537836132327 131143787489237306754198491)
      ·
        refine ⟨196715681233855960131297737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131143787489237306754198491 196715681233855960131297737)
        ·
          refine ⟨147536760925391970098473303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196715681233855960131297737 147536760925391970098473303)
          ·
            refine ⟨221305141388087955147709955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147536760925391970098473303 221305141388087955147709955)
            ·
              refine ⟨331957712082131932721564933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221305141388087955147709955 331957712082131932721564933)
              ·
                refine ⟨62242071015399737385293425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 331957712082131932721564933 62242071015399737385293425)
                ·
                  refine ⟨46681553261549803038970069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62242071015399737385293425 46681553261549803038970069)
                  ·
                    refine ⟨1094098904567573508725861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46681553261549803038970069 1094098904567573508725861)
                    ·
                      rfl

theorem cell23_6392250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 2, 7].length) (baseStart_6392250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6392250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6392250 prefixEnd_6392250 := by exact prefixLift 6392250
  have htrace : WordTrace (prefixWord ++ tailWord_6392250) baseStart_6392250 baseEnd_6392250 := by
    simpa [prefixWord, tailWord_6392250, baseEnd_6392250] using wordTrace_append hprefix tailTrace_6392250
  have hstable : (prefixWord ++ tailWord_6392250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6392250).length < 2 ^ (prefixWord ++ tailWord_6392250).sum := by decide
  have hdescent : baseEnd_6392250 < baseStart_6392250 := by decide
  rcases family_descends (prefixWord ++ tailWord_6392250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6392264 : List Nat := [2, 1, 3, 1, 3, 2, 1, 2, 4, 1, 3]
def baseStart_6392264 : Nat := 118140960795 + 6392264 * 2 ^ 59
def prefixEnd_6392264 : Nat := 4983230072969 + 3 ^ 40 * 6392264 * 2
def baseEnd_6392264 : Nat := 3282303902431883471402519

theorem tailTrace_6392264 : CollatzResearch.WordTrace tailWord_6392264 prefixEnd_6392264 3282303902431883471402519 := by
  unfold tailWord_6392264
  simp only [CollatzResearch.WordTrace]
  refine ⟨116572510856963357310347923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155430014475951143080463897 116572510856963357310347923)
  ·
    refine ⟨174858766285445035965521885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116572510856963357310347923 174858766285445035965521885)
    ·
      refine ⟨65572037357041888487070707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174858766285445035965521885 65572037357041888487070707)
      ·
        refine ⟨98358056035562832730606061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65572037357041888487070707 98358056035562832730606061)
        ·
          refine ⟨36884271013336062273977273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98358056035562832730606061 36884271013336062273977273)
          ·
            refine ⟨27663203260002046705482955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36884271013336062273977273 27663203260002046705482955)
            ·
              refine ⟨41494804890003070058224433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27663203260002046705482955 41494804890003070058224433)
              ·
                refine ⟨31121103667502302543668325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41494804890003070058224433 31121103667502302543668325)
                ·
                  refine ⟨5835206937656681726937811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31121103667502302543668325 5835206937656681726937811)
                  ·
                    refine ⟨8752810406485022590406717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5835206937656681726937811 8752810406485022590406717)
                    ·
                      refine ⟨3282303902431883471402519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8752810406485022590406717 3282303902431883471402519)
                      ·
                        rfl

theorem cell23_6392264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 4, 1, 3].length) (baseStart_6392264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6392264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6392264 prefixEnd_6392264 := by exact prefixLift 6392264
  have htrace : WordTrace (prefixWord ++ tailWord_6392264) baseStart_6392264 baseEnd_6392264 := by
    simpa [prefixWord, tailWord_6392264, baseEnd_6392264] using wordTrace_append hprefix tailTrace_6392264
  have hstable : (prefixWord ++ tailWord_6392264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6392264).length < 2 ^ (prefixWord ++ tailWord_6392264).sum := by decide
  have hdescent : baseEnd_6392264 < baseStart_6392264 := by decide
  rcases family_descends (prefixWord ++ tailWord_6392264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6392298 : List Nat := [3, 1, 3, 1, 3, 1, 4, 1, 2, 1, 3]
def baseStart_6392298 : Nat := 118140960795 + 6392298 * 2 ^ 59
def prefixEnd_6392298 : Nat := 4983230072969 + 3 ^ 40 * 6392298 * 2
def baseEnd_6392298 : Nat := 3282321360774136338377363

theorem tailTrace_6392298 : CollatzResearch.WordTrace tailWord_6392298 prefixEnd_6392298 3282321360774136338377363 := by
  unfold tailWord_6392298
  simp only [CollatzResearch.WordTrace]
  refine ⟨58286565448950884606858387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155430841197202358951622365 58286565448950884606858387)
  ·
    refine ⟨87429848173426326910287581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58286565448950884606858387 87429848173426326910287581)
    ·
      refine ⟨32786193065034872591357843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87429848173426326910287581 32786193065034872591357843)
      ·
        refine ⟨49179289597552308887036765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32786193065034872591357843 49179289597552308887036765)
        ·
          refine ⟨18442233599082115832638787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49179289597552308887036765 18442233599082115832638787)
          ·
            refine ⟨27663350398623173748958181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18442233599082115832638787 27663350398623173748958181)
            ·
              refine ⟨5186878199741845077929659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27663350398623173748958181 5186878199741845077929659)
              ·
                refine ⟨7780317299612767616894489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5186878199741845077929659 7780317299612767616894489)
                ·
                  refine ⟨5835237974709575712670867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7780317299612767616894489 5835237974709575712670867)
                  ·
                    refine ⟨8752856962064363569006301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5835237974709575712670867 8752856962064363569006301)
                    ·
                      refine ⟨3282321360774136338377363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8752856962064363569006301 3282321360774136338377363)
                      ·
                        rfl

theorem cell23_6392298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4, 1, 2, 1, 3].length) (baseStart_6392298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6392298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6392298 prefixEnd_6392298 := by exact prefixLift 6392298
  have htrace : WordTrace (prefixWord ++ tailWord_6392298) baseStart_6392298 baseEnd_6392298 := by
    simpa [prefixWord, tailWord_6392298, baseEnd_6392298] using wordTrace_append hprefix tailTrace_6392298
  have hstable : (prefixWord ++ tailWord_6392298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6392298).length < 2 ^ (prefixWord ++ tailWord_6392298).sum := by decide
  have hdescent : baseEnd_6392298 < baseStart_6392298 := by decide
  rcases family_descends (prefixWord ++ tailWord_6392298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6392304 : List Nat := [2, 1, 1, 1, 3, 3, 2, 3, 1, 4, 2]
def baseStart_6392304 : Nat := 118140960795 + 6392304 * 2 ^ 59
def prefixEnd_6392304 : Nat := 4983230072969 + 3 ^ 40 * 6392304 * 2
def baseEnd_6392304 : Nat := 3282324441658063314902335

theorem tailTrace_6392304 : CollatzResearch.WordTrace tailWord_6392304 prefixEnd_6392304 3282324441658063314902335 := by
  unfold tailWord_6392304
  simp only [CollatzResearch.WordTrace]
  refine ⟨116573240316890900726075983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155430987089187867634767977 116573240316890900726075983)
  ·
    refine ⟨174859860475336351089113975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116573240316890900726075983 174859860475336351089113975)
    ·
      refine ⟨262289790713004526633670963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174859860475336351089113975 262289790713004526633670963)
      ·
        refine ⟨393434686069506789950506445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262289790713004526633670963 393434686069506789950506445)
        ·
          refine ⟨147538007276065046231439917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 393434686069506789950506445 147538007276065046231439917)
          ·
            refine ⟨55326752728524392336789969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147538007276065046231439917 55326752728524392336789969)
            ·
              refine ⟨41495064546393294252592477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55326752728524392336789969 41495064546393294252592477)
              ·
                refine ⟨15560649204897485344722179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41495064546393294252592477 15560649204897485344722179)
                ·
                  refine ⟨23340973807346228017083269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15560649204897485344722179 23340973807346228017083269)
                  ·
                    refine ⟨4376432588877417753203113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23340973807346228017083269 4376432588877417753203113)
                    ·
                      refine ⟨3282324441658063314902335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4376432588877417753203113 3282324441658063314902335)
                      ·
                        rfl

theorem cell23_6392304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3, 1, 4, 2].length) (baseStart_6392304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6392304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6392304 prefixEnd_6392304 := by exact prefixLift 6392304
  have htrace : WordTrace (prefixWord ++ tailWord_6392304) baseStart_6392304 baseEnd_6392304 := by
    simpa [prefixWord, tailWord_6392304, baseEnd_6392304] using wordTrace_append hprefix tailTrace_6392304
  have hstable : (prefixWord ++ tailWord_6392304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6392304).length < 2 ^ (prefixWord ++ tailWord_6392304).sum := by decide
  have hdescent : baseEnd_6392304 < baseStart_6392304 := by decide
  rcases family_descends (prefixWord ++ tailWord_6392304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6392321 : List Nat := [1, 2, 4, 1, 3, 2, 1, 2, 1, 4, 2]
def baseStart_6392321 : Nat := 118140960795 + 6392321 * 2 ^ 59
def prefixEnd_6392321 : Nat := 4983230072969 + 3 ^ 40 * 6392321 * 2
def baseEnd_6392321 : Nat := 3282333170829189748389757

theorem tailTrace_6392321 : CollatzResearch.WordTrace tailWord_6392321 prefixEnd_6392321 3282333170829189748389757 := by
  unfold tailWord_6392321
  simp only [CollatzResearch.WordTrace]
  refine ⟨233147100674720213355520817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155431400449813475570347211 233147100674720213355520817)
  ·
    refine ⟨174860325506040160016640613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233147100674720213355520817 174860325506040160016640613)
    ·
      refine ⟨32786311032382530003120115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 174860325506040160016640613 32786311032382530003120115)
      ·
        refine ⟨49179466548573795004680173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32786311032382530003120115 49179466548573795004680173)
        ·
          refine ⟨18442299955715173126755065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49179466548573795004680173 18442299955715173126755065)
          ·
            refine ⟨13831724966786379845066299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18442299955715173126755065 13831724966786379845066299)
            ·
              refine ⟨20747587450179569767599449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13831724966786379845066299 20747587450179569767599449)
              ·
                refine ⟨15560690587634677325699587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20747587450179569767599449 15560690587634677325699587)
                ·
                  refine ⟨23341035881452015988549381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15560690587634677325699587 23341035881452015988549381)
                  ·
                    refine ⟨4376444227772252997853009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23341035881452015988549381 4376444227772252997853009)
                    ·
                      refine ⟨3282333170829189748389757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4376444227772252997853009 3282333170829189748389757)
                      ·
                        rfl

theorem cell23_6392321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 2, 1, 4, 2].length) (baseStart_6392321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6392321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6392321 prefixEnd_6392321 := by exact prefixLift 6392321
  have htrace : WordTrace (prefixWord ++ tailWord_6392321) baseStart_6392321 baseEnd_6392321 := by
    simpa [prefixWord, tailWord_6392321, baseEnd_6392321] using wordTrace_append hprefix tailTrace_6392321
  have hstable : (prefixWord ++ tailWord_6392321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6392321).length < 2 ^ (prefixWord ++ tailWord_6392321).sum := by decide
  have hdescent : baseEnd_6392321 < baseStart_6392321 := by decide
  rcases family_descends (prefixWord ++ tailWord_6392321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6392324 : List Nat := [2, 3, 2, 3, 1, 1, 2, 1, 2, 1, 5]
def baseStart_6392324 : Nat := 118140960795 + 6392324 * 2 ^ 59
def prefixEnd_6392324 : Nat := 4983230072969 + 3 ^ 40 * 6392324 * 2
def baseEnd_6392324 : Nat := 3282334711271153236652243

theorem tailTrace_6392324 : CollatzResearch.WordTrace tailWord_6392324 prefixEnd_6392324 3282334711271153236652243 := by
  unfold tailWord_6392324
  simp only [CollatzResearch.WordTrace]
  refine ⟨116573605046854672433940013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155431473395806229911920017 116573605046854672433940013)
  ·
    refine ⟨43715101892570502162727505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116573605046854672433940013 43715101892570502162727505)
    ·
      refine ⟨32786326419427876622045629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43715101892570502162727505 32786326419427876622045629)
      ·
        refine ⟨12294872407285453733267111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32786326419427876622045629 12294872407285453733267111)
        ·
          refine ⟨18442308610928180599900667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12294872407285453733267111 18442308610928180599900667)
          ·
            refine ⟨27663462916392270899851001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18442308610928180599900667 27663462916392270899851001)
            ·
              refine ⟨20747597187294203174888251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27663462916392270899851001 20747597187294203174888251)
              ·
                refine ⟨31121395780941304762332377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20747597187294203174888251 31121395780941304762332377)
                ·
                  refine ⟨23341046835705978571749283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31121395780941304762332377 23341046835705978571749283)
                  ·
                    refine ⟨35011570253558967857623925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23341046835705978571749283 35011570253558967857623925)
                    ·
                      refine ⟨3282334711271153236652243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35011570253558967857623925 3282334711271153236652243)
                      ·
                        rfl

theorem cell23_6392324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_6392324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6392324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6392324 prefixEnd_6392324 := by exact prefixLift 6392324
  have htrace : WordTrace (prefixWord ++ tailWord_6392324) baseStart_6392324 baseEnd_6392324 := by
    simpa [prefixWord, tailWord_6392324, baseEnd_6392324] using wordTrace_append hprefix tailTrace_6392324
  have hstable : (prefixWord ++ tailWord_6392324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6392324).length < 2 ^ (prefixWord ++ tailWord_6392324).sum := by decide
  have hdescent : baseEnd_6392324 < baseStart_6392324 := by decide
  rcases family_descends (prefixWord ++ tailWord_6392324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6392357 : List Nat := [1, 3, 1, 2, 2, 1, 2, 2, 4, 5]
def baseStart_6392357 : Nat := 118140960795 + 6392357 * 2 ^ 59
def prefixEnd_6392357 : Nat := 4983230072969 + 3 ^ 40 * 6392357 * 2
def baseEnd_6392357 : Nat := 1094117218710917202513197

theorem tailTrace_6392357 : CollatzResearch.WordTrace tailWord_6392357 prefixEnd_6392357 1094117218710917202513197 := by
  unfold tailWord_6392357
  simp only [CollatzResearch.WordTrace]
  refine ⟨233148413702589791503831325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155432275801726527669220883 233148413702589791503831325)
  ·
    refine ⟨87430655138471171813936747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233148413702589791503831325 87430655138471171813936747)
    ·
      refine ⟨131145982707706757720905121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87430655138471171813936747 131145982707706757720905121)
      ·
        refine ⟨98359487030780068290678841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131145982707706757720905121 98359487030780068290678841)
        ·
          refine ⟨73769615273085051218009131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98359487030780068290678841 73769615273085051218009131)
          ·
            refine ⟨110654422909627576827013697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73769615273085051218009131 110654422909627576827013697)
            ·
              refine ⟨82990817182220682620260273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110654422909627576827013697 82990817182220682620260273)
              ·
                refine ⟨62243112886665511965195205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82990817182220682620260273 62243112886665511965195205)
                ·
                  refine ⟨11670583666249783493474101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62243112886665511965195205 11670583666249783493474101)
                  ·
                    refine ⟨1094117218710917202513197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11670583666249783493474101 1094117218710917202513197)
                    ·
                      rfl

theorem cell23_6392357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 4, 5].length) (baseStart_6392357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6392357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6392357 prefixEnd_6392357 := by exact prefixLift 6392357
  have htrace : WordTrace (prefixWord ++ tailWord_6392357) baseStart_6392357 baseEnd_6392357 := by
    simpa [prefixWord, tailWord_6392357, baseEnd_6392357] using wordTrace_append hprefix tailTrace_6392357
  have hstable : (prefixWord ++ tailWord_6392357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6392357).length < 2 ^ (prefixWord ++ tailWord_6392357).sum := by decide
  have hdescent : baseEnd_6392357 < baseStart_6392357 := by decide
  rcases family_descends (prefixWord ++ tailWord_6392357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6392407 : List Nat := [1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 6]
def baseStart_6392407 : Nat := 118140960795 + 6392407 * 2 ^ 59
def prefixEnd_6392407 : Nat := 4983230072969 + 3 ^ 40 * 6392407 * 2
def baseEnd_6392407 : Nat := 3282377330165476411914361

theorem tailTrace_6392407 : CollatzResearch.WordTrace tailWord_6392407 prefixEnd_6392407 3282377330165476411914361 := by
  unfold tailWord_6392407
  simp only [CollatzResearch.WordTrace]
  refine ⟨233150237352408650043151475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155433491568272433362100983 233150237352408650043151475)
  ·
    refine ⟨349725356028612975064727213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233150237352408650043151475 349725356028612975064727213)
    ·
      refine ⟨131147008510729865649272705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 349725356028612975064727213 131147008510729865649272705)
      ·
        refine ⟨98360256383047399236954529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131147008510729865649272705 98360256383047399236954529)
        ·
          refine ⟨73770192287285549427715897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98360256383047399236954529 73770192287285549427715897)
          ·
            refine ⟨55327644215464162070786923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73770192287285549427715897 55327644215464162070786923)
            ·
              refine ⟨82991466323196243106180385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55327644215464162070786923 82991466323196243106180385)
              ·
                refine ⟨62243599742397182329635289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82991466323196243106180385 62243599742397182329635289)
                ·
                  refine ⟨46682699806797886747226467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62243599742397182329635289 46682699806797886747226467)
                  ·
                    refine ⟨70024049710196830120839701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46682699806797886747226467 70024049710196830120839701)
                    ·
                      refine ⟨3282377330165476411914361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70024049710196830120839701 3282377330165476411914361)
                      ·
                        rfl

theorem cell23_6392407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_6392407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6392407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6392407 prefixEnd_6392407 := by exact prefixLift 6392407
  have htrace : WordTrace (prefixWord ++ tailWord_6392407) baseStart_6392407 baseEnd_6392407 := by
    simpa [prefixWord, tailWord_6392407, baseEnd_6392407] using wordTrace_append hprefix tailTrace_6392407
  have hstable : (prefixWord ++ tailWord_6392407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6392407).length < 2 ^ (prefixWord ++ tailWord_6392407).sum := by decide
  have hdescent : baseEnd_6392407 < baseStart_6392407 := by decide
  rcases family_descends (prefixWord ++ tailWord_6392407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6392457 : List Nat := [1, 2, 1, 1, 4, 1, 1, 2, 2, 1, 7]
def baseStart_6392457 : Nat := 118140960795 + 6392457 * 2 ^ 59
def prefixEnd_6392457 : Nat := 4983230072969 + 3 ^ 40 * 6392457 * 2
def baseEnd_6392457 : Nat := 3282403004198201216289131

theorem tailTrace_6392457 : CollatzResearch.WordTrace tailWord_6392457 prefixEnd_6392457 3282403004198201216289131 := by
  unfold tailWord_6392457
  simp only [CollatzResearch.WordTrace]
  refine ⟨233152061002227508582471625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155434707334818339054981083 233152061002227508582471625)
  ·
    refine ⟨174864045751670631436853719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233152061002227508582471625 174864045751670631436853719)
    ·
      refine ⟨262296068627505947155280579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174864045751670631436853719 262296068627505947155280579)
      ·
        refine ⟨393444102941258920732920869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262296068627505947155280579 393444102941258920732920869)
        ·
          refine ⟨73770769301486047637422663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 393444102941258920732920869 73770769301486047637422663)
          ·
            refine ⟨110656153952229071456133995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73770769301486047637422663 110656153952229071456133995)
            ·
              refine ⟨165984230928343607184200993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110656153952229071456133995 165984230928343607184200993)
              ·
                refine ⟨124488173196257705388150745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165984230928343607184200993 124488173196257705388150745)
                ·
                  refine ⟨93366129897193279041113059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124488173196257705388150745 93366129897193279041113059)
                  ·
                    refine ⟨140049194845789918561669589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 93366129897193279041113059 140049194845789918561669589)
                    ·
                      refine ⟨3282403004198201216289131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 140049194845789918561669589 3282403004198201216289131)
                      ·
                        rfl

theorem cell23_6392457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 1, 7].length) (baseStart_6392457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6392457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6392457 prefixEnd_6392457 := by exact prefixLift 6392457
  have htrace : WordTrace (prefixWord ++ tailWord_6392457) baseStart_6392457 baseEnd_6392457 := by
    simpa [prefixWord, tailWord_6392457, baseEnd_6392457] using wordTrace_append hprefix tailTrace_6392457
  have hstable : (prefixWord ++ tailWord_6392457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6392457).length < 2 ^ (prefixWord ++ tailWord_6392457).sum := by decide
  have hdescent : baseEnd_6392457 < baseStart_6392457 := by decide
  rcases family_descends (prefixWord ++ tailWord_6392457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6392468 : List Nat := [2, 4, 2, 2, 1, 1, 4, 1, 6]
def baseStart_6392468 : Nat := 118140960795 + 6392468 * 2 ^ 59
def prefixEnd_6392468 : Nat := 4983230072969 + 3 ^ 40 * 6392468 * 2
def baseEnd_6392468 : Nat := 364712072498377852583509

theorem tailTrace_6392468 : CollatzResearch.WordTrace tailWord_6392468 prefixEnd_6392468 364712072498377852583509 := by
  unfold tailWord_6392468
  simp only [CollatzResearch.WordTrace]
  refine ⟨116576231102593828730561029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155434974803458438307414705 116576231102593828730561029)
  ·
    refine ⟨21858043331736342886980193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116576231102593828730561029 21858043331736342886980193)
    ·
      refine ⟨16393532498802257165235145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21858043331736342886980193 16393532498802257165235145)
      ·
        refine ⟨12295149374101692873926359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16393532498802257165235145 12295149374101692873926359)
        ·
          refine ⟨18442724061152539310889539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12295149374101692873926359 18442724061152539310889539)
          ·
            refine ⟨27664086091728808966334309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18442724061152539310889539 27664086091728808966334309)
            ·
              refine ⟨5187016142199151681187683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27664086091728808966334309 5187016142199151681187683)
              ·
                refine ⟨7780524213298727521781525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5187016142199151681187683 7780524213298727521781525)
                ·
                  refine ⟨364712072498377852583509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7780524213298727521781525 364712072498377852583509)
                  ·
                    rfl

theorem cell23_6392468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4, 1, 6].length) (baseStart_6392468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6392468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6392468 prefixEnd_6392468 := by exact prefixLift 6392468
  have htrace : WordTrace (prefixWord ++ tailWord_6392468) baseStart_6392468 baseEnd_6392468 := by
    simpa [prefixWord, tailWord_6392468, baseEnd_6392468] using wordTrace_append hprefix tailTrace_6392468
  have hstable : (prefixWord ++ tailWord_6392468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6392468).length < 2 ^ (prefixWord ++ tailWord_6392468).sum := by decide
  have hdescent : baseEnd_6392468 < baseStart_6392468 := by decide
  rcases family_descends (prefixWord ++ tailWord_6392468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6392471 : List Nat := [1, 1, 3, 3, 2, 1, 1, 2, 4, 3, 2]
def baseStart_6392471 : Nat := 118140960795 + 6392471 * 2 ^ 59
def prefixEnd_6392471 : Nat := 4983230072969 + 3 ^ 40 * 6392471 * 2
def baseEnd_6392471 : Nat := 3282410192927364161514067

theorem tailTrace_6392471 : CollatzResearch.WordTrace tailWord_6392471 prefixEnd_6392471 3282410192927364161514067 := by
  unfold tailWord_6392471
  simp only [CollatzResearch.WordTrace]
  refine ⟨233152571624176788973481267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155435047749451192648987511 233152571624176788973481267)
  ·
    refine ⟨349728857436265183460221901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233152571624176788973481267 349728857436265183460221901)
    ·
      refine ⟨131148321538599443797583213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 349728857436265183460221901 131148321538599443797583213)
      ·
        refine ⟨49180620576974791424093705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131148321538599443797583213 49180620576974791424093705)
        ·
          refine ⟨36885465432731093568070279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49180620576974791424093705 36885465432731093568070279)
          ·
            refine ⟨55328198149096640352105419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36885465432731093568070279 55328198149096640352105419)
            ·
              refine ⟨82992297223644960528158129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55328198149096640352105419 82992297223644960528158129)
              ·
                refine ⟨62244222917733720396118597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82992297223644960528158129 62244222917733720396118597)
                ·
                  refine ⟨11670791797075072574272237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62244222917733720396118597 11670791797075072574272237)
                  ·
                    refine ⟨4376546923903152215352089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11670791797075072574272237 4376546923903152215352089)
                    ·
                      refine ⟨3282410192927364161514067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4376546923903152215352089 3282410192927364161514067)
                      ·
                        rfl

theorem cell23_6392471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 4, 3, 2].length) (baseStart_6392471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6392471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6392471 prefixEnd_6392471 := by exact prefixLift 6392471
  have htrace : WordTrace (prefixWord ++ tailWord_6392471) baseStart_6392471 baseEnd_6392471 := by
    simpa [prefixWord, tailWord_6392471, baseEnd_6392471] using wordTrace_append hprefix tailTrace_6392471
  have hstable : (prefixWord ++ tailWord_6392471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6392471).length < 2 ^ (prefixWord ++ tailWord_6392471).sum := by decide
  have hdescent : baseEnd_6392471 < baseStart_6392471 := by decide
  rcases family_descends (prefixWord ++ tailWord_6392471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6392478 : List Nat := [4, 3, 1, 1, 1, 1, 2, 1, 5, 1, 3]
def baseStart_6392478 : Nat := 118140960795 + 6392478 * 2 ^ 59
def prefixEnd_6392478 : Nat := 4983230072969 + 3 ^ 40 * 6392478 * 2
def baseEnd_6392478 : Nat := 3282413787291945634126535

theorem tailTrace_6392478 : CollatzResearch.WordTrace tailWord_6392478 prefixEnd_6392478 3282413787291945634126535 := by
  unfold tailWord_6392478
  simp only [CollatzResearch.WordTrace]
  refine ⟨29144103366893928646123261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155435217956767619445990725 29144103366893928646123261)
  ·
    refine ⟨10929038762585223242296223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29144103366893928646123261 10929038762585223242296223)
    ·
      refine ⟨16393558143877834863444335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10929038762585223242296223 16393558143877834863444335)
      ·
        refine ⟨24590337215816752295166503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16393558143877834863444335 24590337215816752295166503)
        ·
          refine ⟨36885505823725128442749755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24590337215816752295166503 36885505823725128442749755)
          ·
            refine ⟨55328258735587692664124633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36885505823725128442749755 55328258735587692664124633)
            ·
              refine ⟨41496194051690769498093475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55328258735587692664124633 41496194051690769498093475)
              ·
                refine ⟨62244291077536154247140213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41496194051690769498093475 62244291077536154247140213)
                ·
                  refine ⟨5835402288519014460669395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62244291077536154247140213 5835402288519014460669395)
                  ·
                    refine ⟨8753103432778521691004093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5835402288519014460669395 8753103432778521691004093)
                    ·
                      refine ⟨3282413787291945634126535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8753103432778521691004093 3282413787291945634126535)
                      ·
                        rfl

theorem cell23_6392478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_6392478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6392478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6392478 prefixEnd_6392478 := by exact prefixLift 6392478
  have htrace : WordTrace (prefixWord ++ tailWord_6392478) baseStart_6392478 baseEnd_6392478 := by
    simpa [prefixWord, tailWord_6392478, baseEnd_6392478] using wordTrace_append hprefix tailTrace_6392478
  have hstable : (prefixWord ++ tailWord_6392478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6392478).length < 2 ^ (prefixWord ++ tailWord_6392478).sum := by decide
  have hdescent : baseEnd_6392478 < baseStart_6392478 := by decide
  rcases family_descends (prefixWord ++ tailWord_6392478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6392481 : List Nat := [1, 2, 3, 3, 3, 1, 1, 1, 3, 5]
def baseStart_6392481 : Nat := 118140960795 + 6392481 * 2 ^ 59
def prefixEnd_6392481 : Nat := 4983230072969 + 3 ^ 40 * 6392481 * 2
def baseEnd_6392481 : Nat := 1094138442577969707463007

theorem tailTrace_6392481 : CollatzResearch.WordTrace tailWord_6392481 prefixEnd_6392481 1094138442577969707463007 := by
  unfold tailWord_6392481
  simp only [CollatzResearch.WordTrace]
  refine ⟨233152936354140560681345297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155435290902760373787563531 233152936354140560681345297)
  ·
    refine ⟨174864702265605420511008973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233152936354140560681345297 174864702265605420511008973)
    ·
      refine ⟨65574263349602032691628365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174864702265605420511008973 65574263349602032691628365)
      ·
        refine ⟨24590348756100762259360637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65574263349602032691628365 24590348756100762259360637)
        ·
          refine ⟨9221380783537785847260239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24590348756100762259360637 9221380783537785847260239)
          ·
            refine ⟨13832071175306678770890359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9221380783537785847260239 13832071175306678770890359)
            ·
              refine ⟨20748106762960018156335539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13832071175306678770890359 20748106762960018156335539)
              ·
                refine ⟨31122160144440027234503309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20748106762960018156335539 31122160144440027234503309)
                ·
                  refine ⟨11670810054165010212938741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31122160144440027234503309 11670810054165010212938741)
                  ·
                    refine ⟨1094138442577969707463007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11670810054165010212938741 1094138442577969707463007)
                    ·
                      rfl

theorem cell23_6392481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 3, 5].length) (baseStart_6392481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6392481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6392481 prefixEnd_6392481 := by exact prefixLift 6392481
  have htrace : WordTrace (prefixWord ++ tailWord_6392481) baseStart_6392481 baseEnd_6392481 := by
    simpa [prefixWord, tailWord_6392481, baseEnd_6392481] using wordTrace_append hprefix tailTrace_6392481
  have hstable : (prefixWord ++ tailWord_6392481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6392481).length < 2 ^ (prefixWord ++ tailWord_6392481).sum := by decide
  have hdescent : baseEnd_6392481 < baseStart_6392481 := by decide
  rcases family_descends (prefixWord ++ tailWord_6392481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6392511 : List Nat := [1, 1, 2, 2, 2, 4, 1, 4, 2, 4]
def baseStart_6392511 : Nat := 118140960795 + 6392511 * 2 ^ 59
def prefixEnd_6392511 : Nat := 4983230072969 + 3 ^ 40 * 6392511 * 2
def baseEnd_6392511 : Nat := 1094143577384514668337961

theorem tailTrace_6392511 : CollatzResearch.WordTrace tailWord_6392511 prefixEnd_6392511 1094143577384514668337961 := by
  unfold tailWord_6392511
  simp only [CollatzResearch.WordTrace]
  refine ⟨233154030544031875804937387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155436020362687917203291591 233154030544031875804937387)
  ·
    refine ⟨349731045816047813707406081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233154030544031875804937387 349731045816047813707406081)
    ·
      refine ⟨262298284362035860280554561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 349731045816047813707406081 262298284362035860280554561)
      ·
        refine ⟨196723713271526895210415921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262298284362035860280554561 196723713271526895210415921)
        ·
          refine ⟨147542784953645171407811941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196723713271526895210415921 147542784953645171407811941)
          ·
            refine ⟨27664272178808469638964739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 147542784953645171407811941 27664272178808469638964739)
            ·
              refine ⟨41496408268212704458447109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27664272178808469638964739 41496408268212704458447109)
              ·
                refine ⟨7780576550289882085958833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41496408268212704458447109 7780576550289882085958833)
                ·
                  refine ⟨5835432412717411564469125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7780576550289882085958833 5835432412717411564469125)
                  ·
                    refine ⟨1094143577384514668337961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5835432412717411564469125 1094143577384514668337961)
                    ·
                      rfl

theorem cell23_6392511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 4, 2, 4].length) (baseStart_6392511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6392511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6392511 prefixEnd_6392511 := by exact prefixLift 6392511
  have htrace : WordTrace (prefixWord ++ tailWord_6392511) baseStart_6392511 baseEnd_6392511 := by
    simpa [prefixWord, tailWord_6392511, baseEnd_6392511] using wordTrace_append hprefix tailTrace_6392511
  have hstable : (prefixWord ++ tailWord_6392511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6392511).length < 2 ^ (prefixWord ++ tailWord_6392511).sum := by decide
  have hdescent : baseEnd_6392511 < baseStart_6392511 := by decide
  rcases family_descends (prefixWord ++ tailWord_6392511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6392512 : List Nat := [2, 1, 1, 2, 4, 4, 2, 2, 1, 1, 3]
def baseStart_6392512 : Nat := 118140960795 + 6392512 * 2 ^ 59
def prefixEnd_6392512 : Nat := 4983230072969 + 3 ^ 40 * 6392512 * 2
def baseEnd_6392512 : Nat := 3282431245634198501101379

theorem tailTrace_6392512 : CollatzResearch.WordTrace tailWord_6392512 prefixEnd_6392512 3282431245634198501101379 := by
  unfold tailWord_6392512
  simp only [CollatzResearch.WordTrace]
  refine ⟨116577033508514126487861895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155436044678018835317149193 116577033508514126487861895)
  ·
    refine ⟨174865550262771189731792843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116577033508514126487861895 174865550262771189731792843)
    ·
      refine ⟨262298325394156784597689265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174865550262771189731792843 262298325394156784597689265)
      ·
        refine ⟨196723744045617588448266949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262298325394156784597689265 196723744045617588448266949)
        ·
          refine ⟨36885702008553297834050053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 196723744045617588448266949 36885702008553297834050053)
          ·
            refine ⟨6916069126603743343884385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36885702008553297834050053 6916069126603743343884385)
            ·
              refine ⟨5187051844952807507913289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6916069126603743343884385 5187051844952807507913289)
              ·
                refine ⟨3890288883714605630934967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5187051844952807507913289 3890288883714605630934967)
                ·
                  refine ⟨5835433325571908446402451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3890288883714605630934967 5835433325571908446402451)
                  ·
                    refine ⟨8753149988357862669603677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5835433325571908446402451 8753149988357862669603677)
                    ·
                      refine ⟨3282431245634198501101379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8753149988357862669603677 3282431245634198501101379)
                      ·
                        rfl

theorem cell23_6392512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2, 2, 1, 1, 3].length) (baseStart_6392512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6392512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6392512 prefixEnd_6392512 := by exact prefixLift 6392512
  have htrace : WordTrace (prefixWord ++ tailWord_6392512) baseStart_6392512 baseEnd_6392512 := by
    simpa [prefixWord, tailWord_6392512, baseEnd_6392512] using wordTrace_append hprefix tailTrace_6392512
  have hstable : (prefixWord ++ tailWord_6392512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6392512).length < 2 ^ (prefixWord ++ tailWord_6392512).sum := by decide
  have hdescent : baseEnd_6392512 < baseStart_6392512 := by decide
  rcases family_descends (prefixWord ++ tailWord_6392512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6392552 : List Nat := [2, 1, 4, 1, 5, 1, 2, 1, 1, 1, 4]
def baseStart_6392552 : Nat := 118140960795 + 6392552 * 2 ^ 59
def prefixEnd_6392552 : Nat := 4983230072969 + 3 ^ 40 * 6392552 * 2
def baseEnd_6392552 : Nat := 3282451784860378344601195

theorem tailTrace_6392552 : CollatzResearch.WordTrace tailWord_6392552 prefixEnd_6392552 3282451784860378344601195 := by
  unfold tailWord_6392552
  simp only [CollatzResearch.WordTrace]
  refine ⟨116577762968441669903589955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155437017291255559871453273 116577762968441669903589955)
  ·
    refine ⟨174866644452662504855384933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116577762968441669903589955 174866644452662504855384933)
    ·
      refine ⟨32787495834874219660384675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 174866644452662504855384933 32787495834874219660384675)
      ·
        refine ⟨49181243752311329490577013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32787495834874219660384675 49181243752311329490577013)
        ·
          refine ⟨4610741601779187139741595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49181243752311329490577013 4610741601779187139741595)
          ·
            refine ⟨6916112402668780709612393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4610741601779187139741595 6916112402668780709612393)
            ·
              refine ⟨5187084302001585532209295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6916112402668780709612393 5187084302001585532209295)
              ·
                refine ⟨7780626453002378298313943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5187084302001585532209295 7780626453002378298313943)
                ·
                  refine ⟨11670939679503567447470915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7780626453002378298313943 11670939679503567447470915)
                  ·
                    refine ⟨17506409519255351171206373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11670939679503567447470915 17506409519255351171206373)
                    ·
                      refine ⟨3282451784860378344601195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17506409519255351171206373 3282451784860378344601195)
                      ·
                        rfl

theorem cell23_6392552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 2, 1, 1, 1, 4].length) (baseStart_6392552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6392552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6392552 prefixEnd_6392552 := by exact prefixLift 6392552
  have htrace : WordTrace (prefixWord ++ tailWord_6392552) baseStart_6392552 baseEnd_6392552 := by
    simpa [prefixWord, tailWord_6392552, baseEnd_6392552] using wordTrace_append hprefix tailTrace_6392552
  have hstable : (prefixWord ++ tailWord_6392552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6392552).length < 2 ^ (prefixWord ++ tailWord_6392552).sum := by decide
  have hdescent : baseEnd_6392552 < baseStart_6392552 := by decide
  rcases family_descends (prefixWord ++ tailWord_6392552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6392625 : List Nat := [1, 2, 2, 3, 2, 1, 2, 4, 2, 2, 2]
def baseStart_6392625 : Nat := 118140960795 + 6392625 * 2 ^ 59
def prefixEnd_6392625 : Nat := 4983230072969 + 3 ^ 40 * 6392625 * 2
def baseEnd_6392625 : Nat := 3282489268948156558988359

theorem tailTrace_6392625 : CollatzResearch.WordTrace tailWord_6392625 prefixEnd_6392625 3282489268948156558988359 := by
  unfold tailWord_6392625
  simp only [CollatzResearch.WordTrace]
  refine ⟨233158188465618873274587329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155438792310412582183058219 233158188465618873274587329)
  ·
    refine ⟨174868641349214154955940497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233158188465618873274587329 174868641349214154955940497)
    ·
      refine ⟨131151481011910616216955373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174868641349214154955940497 131151481011910616216955373)
      ·
        refine ⟨49181805379466481081358265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131151481011910616216955373 49181805379466481081358265)
        ·
          refine ⟨36886354034599860811018699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49181805379466481081358265 36886354034599860811018699)
          ·
            refine ⟨55329531051899791216528049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36886354034599860811018699 55329531051899791216528049)
            ·
              refine ⟨41497148288924843412396037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55329531051899791216528049 41497148288924843412396037)
              ·
                refine ⟨7780715304173408139824257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41497148288924843412396037 7780715304173408139824257)
                ·
                  refine ⟨5835536478130056104868193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7780715304173408139824257 5835536478130056104868193)
                  ·
                    refine ⟨4376652358597542078651145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5835536478130056104868193 4376652358597542078651145)
                    ·
                      refine ⟨3282489268948156558988359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4376652358597542078651145 3282489268948156558988359)
                      ·
                        rfl

theorem cell23_6392625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 4, 2, 2, 2].length) (baseStart_6392625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6392625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6392625 prefixEnd_6392625 := by exact prefixLift 6392625
  have htrace : WordTrace (prefixWord ++ tailWord_6392625) baseStart_6392625 baseEnd_6392625 := by
    simpa [prefixWord, tailWord_6392625, baseEnd_6392625] using wordTrace_append hprefix tailTrace_6392625
  have hstable : (prefixWord ++ tailWord_6392625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6392625).length < 2 ^ (prefixWord ++ tailWord_6392625).sum := by decide
  have hdescent : baseEnd_6392625 < baseStart_6392625 := by decide
  rcases family_descends (prefixWord ++ tailWord_6392625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6392646 : List Nat := [6, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2]
def baseStart_6392646 : Nat := 118140960795 + 6392646 * 2 ^ 59
def prefixEnd_6392646 : Nat := 4983230072969 + 3 ^ 40 * 6392646 * 2
def baseEnd_6392646 : Nat := 3282500052041900976825763

theorem tailTrace_6392646 : CollatzResearch.WordTrace tailWord_6392646 prefixEnd_6392646 3282500052041900976825763 := by
  unfold tailWord_6392646
  simp only [CollatzResearch.WordTrace]
  refine ⟨7286217324954462308159431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 155439302932361862574067861 7286217324954462308159431)
  ·
    refine ⟨10929325987431693462239147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7286217324954462308159431 10929325987431693462239147)
    ·
      refine ⟨16393988981147540193358721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10929325987431693462239147 16393988981147540193358721)
      ·
        refine ⟨12295491735860655145019041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16393988981147540193358721 12295491735860655145019041)
        ·
          refine ⟨9221618801895491358764281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12295491735860655145019041 9221618801895491358764281)
          ·
            refine ⟨6916214101421618519073211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9221618801895491358764281 6916214101421618519073211)
            ·
              refine ⟨10374321152132427778609817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6916214101421618519073211 10374321152132427778609817)
              ·
                refine ⟨7780740864099320833957363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10374321152132427778609817 7780740864099320833957363)
                ·
                  refine ⟨11671111296148981250936045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7780740864099320833957363 11671111296148981250936045)
                  ·
                    refine ⟨4376666736055867969101017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11671111296148981250936045 4376666736055867969101017)
                    ·
                      refine ⟨3282500052041900976825763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4376666736055867969101017 3282500052041900976825763)
                      ·
                        rfl

theorem cell23_6392646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_6392646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6392646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6392646 prefixEnd_6392646 := by exact prefixLift 6392646
  have htrace : WordTrace (prefixWord ++ tailWord_6392646) baseStart_6392646 baseEnd_6392646 := by
    simpa [prefixWord, tailWord_6392646, baseEnd_6392646] using wordTrace_append hprefix tailTrace_6392646
  have hstable : (prefixWord ++ tailWord_6392646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6392646).length < 2 ^ (prefixWord ++ tailWord_6392646).sum := by decide
  have hdescent : baseEnd_6392646 < baseStart_6392646 := by decide
  rcases family_descends (prefixWord ++ tailWord_6392646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6392725 : List Nat := [1, 3, 2, 1, 1, 4, 1, 5, 1, 4]
def baseStart_6392725 : Nat := 118140960795 + 6392725 * 2 ^ 59
def prefixEnd_6392725 : Nat := 4983230072969 + 3 ^ 40 * 6392725 * 2
def baseEnd_6392725 : Nat := 1094180205671202055912633

theorem tailTrace_6392725 : CollatzResearch.WordTrace tailWord_6392725 prefixEnd_6392725 1094180205671202055912633 := by
  unfold tailWord_6392725
  simp only [CollatzResearch.WordTrace]
  refine ⟨233161835765256590353227629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155441223843504393568818419 233161835765256590353227629)
  ·
    refine ⟨87435688411971221382460361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233161835765256590353227629 87435688411971221382460361)
    ·
      refine ⟨65576766308978416036845271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87435688411971221382460361 65576766308978416036845271)
      ·
        refine ⟨98365149463467624055267907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65576766308978416036845271 98365149463467624055267907)
        ·
          refine ⟨147547724195201436082901861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98365149463467624055267907 147547724195201436082901861)
          ·
            refine ⟨27665198286600269265544099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 147547724195201436082901861 27665198286600269265544099)
            ·
              refine ⟨41497797429900403898316149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27665198286600269265544099 41497797429900403898316149)
              ·
                refine ⟨3890418509053162865467139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41497797429900403898316149 3890418509053162865467139)
                ·
                  refine ⟨5835627763579744298200709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3890418509053162865467139 5835627763579744298200709)
                  ·
                    refine ⟨1094180205671202055912633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5835627763579744298200709 1094180205671202055912633)
                    ·
                      rfl

theorem cell23_6392725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 5, 1, 4].length) (baseStart_6392725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6392725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6392725 prefixEnd_6392725 := by exact prefixLift 6392725
  have htrace : WordTrace (prefixWord ++ tailWord_6392725) baseStart_6392725 baseEnd_6392725 := by
    simpa [prefixWord, tailWord_6392725, baseEnd_6392725] using wordTrace_append hprefix tailTrace_6392725
  have hstable : (prefixWord ++ tailWord_6392725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6392725).length < 2 ^ (prefixWord ++ tailWord_6392725).sum := by decide
  have hdescent : baseEnd_6392725 < baseStart_6392725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6392725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6392738 : List Nat := [3, 3, 1, 2, 2, 2, 1, 1, 8]
def baseStart_6392738 : Nat := 118140960795 + 6392738 * 2 ^ 59
def prefixEnd_6392738 : Nat := 4983230072969 + 3 ^ 40 * 6392738 * 2
def baseEnd_6392738 : Nat := 364727476918012735208371

theorem tailTrace_6392738 : CollatzResearch.WordTrace tailWord_6392738 prefixEnd_6392738 364727476918012735208371 := by
  unfold tailWord_6392738
  simp only [CollatzResearch.WordTrace]
  refine ⟨58290577478552373393362717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155441539942806329048967245 58290577478552373393362717)
  ·
    refine ⟨21858966554457140022511019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58290577478552373393362717 21858966554457140022511019)
    ·
      refine ⟨32788449831685710033766529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21858966554457140022511019 32788449831685710033766529)
      ·
        refine ⟨24591337373764282525324897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32788449831685710033766529 24591337373764282525324897)
        ·
          refine ⟨18443503030323211893993673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24591337373764282525324897 18443503030323211893993673)
          ·
            refine ⟨13832627272742408920495255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18443503030323211893993673 13832627272742408920495255)
            ·
              refine ⟨20748940909113613380742883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13832627272742408920495255 20748940909113613380742883)
              ·
                refine ⟨31123411363670420071114325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20748940909113613380742883 31123411363670420071114325)
                ·
                  refine ⟨364727476918012735208371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31123411363670420071114325 364727476918012735208371)
                  ·
                    rfl

theorem cell23_6392738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 8].length) (baseStart_6392738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6392738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6392738 prefixEnd_6392738 := by exact prefixLift 6392738
  have htrace : WordTrace (prefixWord ++ tailWord_6392738) baseStart_6392738 baseEnd_6392738 := by
    simpa [prefixWord, tailWord_6392738, baseEnd_6392738] using wordTrace_append hprefix tailTrace_6392738
  have hstable : (prefixWord ++ tailWord_6392738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6392738).length < 2 ^ (prefixWord ++ tailWord_6392738).sum := by decide
  have hdescent : baseEnd_6392738 < baseStart_6392738 := by decide
  rcases family_descends (prefixWord ++ tailWord_6392738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6392748 : List Nat := [2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 3]
def baseStart_6392748 : Nat := 118140960795 + 6392748 * 2 ^ 59
def prefixEnd_6392748 : Nat := 4983230072969 + 3 ^ 40 * 6392748 * 2
def baseEnd_6392748 : Nat := 3282552427068659577750293

theorem tailTrace_6392748 : CollatzResearch.WordTrace tailWord_6392748 prefixEnd_6392748 3282552427068659577750293 := by
  unfold tailWord_6392748
  simp only [CollatzResearch.WordTrace]
  refine ⟨116581337322086632640657449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155441783096115510187543265 116581337322086632640657449)
  ·
    refine ⟨87436002991564974480493087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116581337322086632640657449 87436002991564974480493087)
    ·
      refine ⟨131154004487347461720739631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87436002991564974480493087 131154004487347461720739631)
      ·
        refine ⟨196731006731021192581109447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131154004487347461720739631 196731006731021192581109447)
        ·
          refine ⟨295096510096531788871664171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196731006731021192581109447 295096510096531788871664171)
          ·
            refine ⟨442644765144797683307496257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295096510096531788871664171 442644765144797683307496257)
            ·
              refine ⟨331983573858598262480622193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 442644765144797683307496257 331983573858598262480622193)
              ·
                refine ⟨248987680393948696860466645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 331983573858598262480622193 248987680393948696860466645)
                ·
                  refine ⟨5835648759233172582667187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 248987680393948696860466645 5835648759233172582667187)
                  ·
                    refine ⟨8753473138849758874000781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5835648759233172582667187 8753473138849758874000781)
                    ·
                      refine ⟨3282552427068659577750293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8753473138849758874000781 3282552427068659577750293)
                      ·
                        rfl

theorem cell23_6392748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 3].length) (baseStart_6392748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6392748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6392748 prefixEnd_6392748 := by exact prefixLift 6392748
  have htrace : WordTrace (prefixWord ++ tailWord_6392748) baseStart_6392748 baseEnd_6392748 := by
    simpa [prefixWord, tailWord_6392748, baseEnd_6392748] using wordTrace_append hprefix tailTrace_6392748
  have hstable : (prefixWord ++ tailWord_6392748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6392748).length < 2 ^ (prefixWord ++ tailWord_6392748).sum := by decide
  have hdescent : baseEnd_6392748 < baseStart_6392748 := by decide
  rcases family_descends (prefixWord ++ tailWord_6392748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6392751 : List Nat := [1, 1, 2, 1, 2, 2, 2, 4, 3, 5]
def baseStart_6392751 : Nat := 118140960795 + 6392751 * 2 ^ 59
def prefixEnd_6392751 : Nat := 4983230072969 + 3 ^ 40 * 6392751 * 2
def baseEnd_6392751 : Nat := 1094184655836874355337593

theorem tailTrace_6392751 : CollatzResearch.WordTrace tailWord_6392751 prefixEnd_6392751 1094184655836874355337593 := by
  unfold tailWord_6392751
  simp only [CollatzResearch.WordTrace]
  refine ⟨233162784063162396793674107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155441856042108264529116071 233162784063162396793674107)
  ·
    refine ⟨349744176094743595190511161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233162784063162396793674107 349744176094743595190511161)
    ·
      refine ⟨262308132071057696392883371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 349744176094743595190511161 262308132071057696392883371)
      ·
        refine ⟨393462198106586544589325057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262308132071057696392883371 393462198106586544589325057)
        ·
          refine ⟨295096648579939908441993793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 393462198106586544589325057 295096648579939908441993793)
          ·
            refine ⟨221322486434954931331495345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295096648579939908441993793 221322486434954931331495345)
            ·
              refine ⟨165991864826216198498621509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221322486434954931331495345 165991864826216198498621509)
              ·
                refine ⟨31123474654915537218491533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 165991864826216198498621509 31123474654915537218491533)
                ·
                  refine ⟨11671302995593326456934325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31123474654915537218491533 11671302995593326456934325)
                  ·
                    refine ⟨1094184655836874355337593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11671302995593326456934325 1094184655836874355337593)
                    ·
                      rfl

theorem cell23_6392751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 3, 5].length) (baseStart_6392751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6392751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6392751 prefixEnd_6392751 := by exact prefixLift 6392751
  have htrace : WordTrace (prefixWord ++ tailWord_6392751) baseStart_6392751 baseEnd_6392751 := by
    simpa [prefixWord, tailWord_6392751, baseEnd_6392751] using wordTrace_append hprefix tailTrace_6392751
  have hstable : (prefixWord ++ tailWord_6392751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6392751).length < 2 ^ (prefixWord ++ tailWord_6392751).sum := by decide
  have hdescent : baseEnd_6392751 < baseStart_6392751 := by decide
  rcases family_descends (prefixWord ++ tailWord_6392751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6392768 : List Nat := [2, 1, 1, 2, 3, 3, 1, 4, 1, 5]
def baseStart_6392768 : Nat := 118140960795 + 6392768 * 2 ^ 59
def prefixEnd_6392768 : Nat := 4983230072969 + 3 ^ 40 * 6392768 * 2
def baseEnd_6392768 : Nat := 1094187565560583166500067

theorem tailTrace_6392768 : CollatzResearch.WordTrace tailWord_6392768 prefixEnd_6392768 1094187565560583166500067 := by
  unfold tailWord_6392768
  simp only [CollatzResearch.WordTrace]
  refine ⟨116581702052050404348521479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155442269402733872464695305 116581702052050404348521479)
  ·
    refine ⟨174872553078075606522782219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116581702052050404348521479 174872553078075606522782219)
    ·
      refine ⟨262308829617113409784173329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174872553078075606522782219 262308829617113409784173329)
      ·
        refine ⟨196731622212835057338129997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262308829617113409784173329 196731622212835057338129997)
        ·
          refine ⟨73774358329813146501798749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196731622212835057338129997 73774358329813146501798749)
          ·
            refine ⟨27665384373679929938174531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73774358329813146501798749 27665384373679929938174531)
            ·
              refine ⟨41498076560519894907261797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27665384373679929938174531 41498076560519894907261797)
              ·
                refine ⟨7780889355097480295111587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41498076560519894907261797 7780889355097480295111587)
                ·
                  refine ⟨11671334032646220442667381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7780889355097480295111587 11671334032646220442667381)
                  ·
                    refine ⟨1094187565560583166500067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11671334032646220442667381 1094187565560583166500067)
                    ·
                      rfl

theorem cell23_6392768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 4, 1, 5].length) (baseStart_6392768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6392768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6392768 prefixEnd_6392768 := by exact prefixLift 6392768
  have htrace : WordTrace (prefixWord ++ tailWord_6392768) baseStart_6392768 baseEnd_6392768 := by
    simpa [prefixWord, tailWord_6392768, baseEnd_6392768] using wordTrace_append hprefix tailTrace_6392768
  have hstable : (prefixWord ++ tailWord_6392768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6392768).length < 2 ^ (prefixWord ++ tailWord_6392768).sum := by decide
  have hdescent : baseEnd_6392768 < baseStart_6392768 := by decide
  rcases family_descends (prefixWord ++ tailWord_6392768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6392799 : List Nat := [1, 1, 2, 3, 6, 1, 1, 1, 3, 1, 3]
def baseStart_6392799 : Nat := 118140960795 + 6392799 * 2 ^ 59
def prefixEnd_6392799 : Nat := 4983230072969 + 3 ^ 40 * 6392799 * 2
def baseEnd_6392799 : Nat := 3282578614582038878212559

theorem tailTrace_6392799 : CollatzResearch.WordTrace tailWord_6392799 prefixEnd_6392799 3282578614582038878212559 := by
  unfold tailWord_6392799
  simp only [CollatzResearch.WordTrace]
  refine ⟨233164534766988500991421451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155443023177992333994280967 233164534766988500991421451)
  ·
    refine ⟨349746802150482751487132177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233164534766988500991421451 349746802150482751487132177)
    ·
      refine ⟨262310101612862063615349133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 349746802150482751487132177 262310101612862063615349133)
      ·
        refine ⟨98366288104823273855755925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 262310101612862063615349133 98366288104823273855755925)
        ·
          refine ⟨4610919754913590961988559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 98366288104823273855755925 4610919754913590961988559)
          ·
            refine ⟨6916379632370386442982839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4610919754913590961988559 6916379632370386442982839)
            ·
              refine ⟨10374569448555579664474259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6916379632370386442982839 10374569448555579664474259)
              ·
                refine ⟨15561854172833369496711389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10374569448555579664474259 15561854172833369496711389)
                ·
                  refine ⟨5835695314812513561266771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15561854172833369496711389 5835695314812513561266771)
                  ·
                    refine ⟨8753542972218770341900157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5835695314812513561266771 8753542972218770341900157)
                    ·
                      refine ⟨3282578614582038878212559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8753542972218770341900157 3282578614582038878212559)
                      ·
                        rfl

theorem cell23_6392799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 1, 3, 1, 3].length) (baseStart_6392799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6392799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6392799 prefixEnd_6392799 := by exact prefixLift 6392799
  have htrace : WordTrace (prefixWord ++ tailWord_6392799) baseStart_6392799 baseEnd_6392799 := by
    simpa [prefixWord, tailWord_6392799, baseEnd_6392799] using wordTrace_append hprefix tailTrace_6392799
  have hstable : (prefixWord ++ tailWord_6392799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6392799).length < 2 ^ (prefixWord ++ tailWord_6392799).sum := by decide
  have hdescent : baseEnd_6392799 < baseStart_6392799 := by decide
  rcases family_descends (prefixWord ++ tailWord_6392799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6392808 : List Nat := [2, 1, 4, 1, 1, 1, 4, 2, 1, 1, 5]
def baseStart_6392808 : Nat := 118140960795 + 6392808 * 2 ^ 59
def prefixEnd_6392808 : Nat := 4983230072969 + 3 ^ 40 * 6392808 * 2
def baseEnd_6392808 : Nat := 3282583235907929343000017

theorem tailTrace_6392808 : CollatzResearch.WordTrace tailWord_6392808 prefixEnd_6392808 3282583235907929343000017 := by
  unfold tailWord_6392808
  simp only [CollatzResearch.WordTrace]
  refine ⟨116582431511977947764249539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155443242015970597018999385 116582431511977947764249539)
  ·
    refine ⟨174873647267966921646374309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116582431511977947764249539 174873647267966921646374309)
    ·
      refine ⟨32788808862743797808695183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 174873647267966921646374309 32788808862743797808695183)
      ·
        refine ⟨49183213294115696713042775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32788808862743797808695183 49183213294115696713042775)
        ·
          refine ⟨73774819941173545069564163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49183213294115696713042775 73774819941173545069564163)
          ·
            refine ⟨110662229911760317604346245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73774819941173545069564163 110662229911760317604346245)
            ·
              refine ⟨20749168108455059550814921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110662229911760317604346245 20749168108455059550814921)
              ·
                refine ⟨15561876081341294663111191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20749168108455059550814921 15561876081341294663111191)
                ·
                  refine ⟨23342814122011941994666787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15561876081341294663111191 23342814122011941994666787)
                  ·
                    refine ⟨35014221183017912992000181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23342814122011941994666787 35014221183017912992000181)
                    ·
                      refine ⟨3282583235907929343000017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35014221183017912992000181 3282583235907929343000017)
                      ·
                        rfl

theorem cell23_6392808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_6392808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6392808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6392808 prefixEnd_6392808 := by exact prefixLift 6392808
  have htrace : WordTrace (prefixWord ++ tailWord_6392808) baseStart_6392808 baseEnd_6392808 := by
    simpa [prefixWord, tailWord_6392808, baseEnd_6392808] using wordTrace_append hprefix tailTrace_6392808
  have hstable : (prefixWord ++ tailWord_6392808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6392808).length < 2 ^ (prefixWord ++ tailWord_6392808).sum := by decide
  have hdescent : baseEnd_6392808 < baseStart_6392808 := by decide
  rcases family_descends (prefixWord ++ tailWord_6392808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6392815 : List Nat := [1, 1, 2, 1, 4, 4, 1, 3, 2, 4]
def baseStart_6392815 : Nat := 118140960795 + 6392815 * 2 ^ 59
def prefixEnd_6392815 : Nat := 4983230072969 + 3 ^ 40 * 6392815 * 2
def baseEnd_6392815 : Nat := 1094195610090836938537495

theorem tailTrace_6392815 : CollatzResearch.WordTrace tailWord_6392815 prefixEnd_6392815 1094195610090836938537495 := by
  unfold tailWord_6392815
  simp only [CollatzResearch.WordTrace]
  refine ⟨233165118334930535724003899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155443412223287023816002599 233165118334930535724003899)
  ·
    refine ⟨349747677502395803586005849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233165118334930535724003899 349747677502395803586005849)
    ·
      refine ⟨262310758126796852689504387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 349747677502395803586005849 262310758126796852689504387)
      ·
        refine ⟨393466137190195279034256581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262310758126796852689504387 393466137190195279034256581)
        ·
          refine ⟨73774900723161614818923109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 393466137190195279034256581 73774900723161614818923109)
          ·
            refine ⟨13832793885592802778548083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73774900723161614818923109 13832793885592802778548083)
            ·
              refine ⟨20749190828389204167822125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13832793885592802778548083 20749190828389204167822125)
              ·
                refine ⟨7780946560645951562933297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20749190828389204167822125 7780946560645951562933297)
                ·
                  refine ⟨5835709920484463672199973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7780946560645951562933297 5835709920484463672199973)
                  ·
                    refine ⟨1094195610090836938537495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5835709920484463672199973 1094195610090836938537495)
                    ·
                      rfl

theorem cell23_6392815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 3, 2, 4].length) (baseStart_6392815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6392815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6392815 prefixEnd_6392815 := by exact prefixLift 6392815
  have htrace : WordTrace (prefixWord ++ tailWord_6392815) baseStart_6392815 baseEnd_6392815 := by
    simpa [prefixWord, tailWord_6392815, baseEnd_6392815] using wordTrace_append hprefix tailTrace_6392815
  have hstable : (prefixWord ++ tailWord_6392815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6392815).length < 2 ^ (prefixWord ++ tailWord_6392815).sum := by decide
  have hdescent : baseEnd_6392815 < baseStart_6392815 := by decide
  rcases family_descends (prefixWord ++ tailWord_6392815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6392822 : List Nat := [5, 1, 1, 1, 3, 1, 3, 2, 1, 1, 4]
def baseStart_6392822 : Nat := 118140960795 + 6392822 * 2 ^ 59
def prefixEnd_6392822 : Nat := 4983230072969 + 3 ^ 40 * 6392822 * 2
def baseEnd_6392822 : Nat := 3282590424637092288224953

theorem tailTrace_6392822 : CollatzResearch.WordTrace tailWord_6392822 prefixEnd_6392822 3282590424637092288224953 := by
  unfold tailWord_6392822
  simp only [CollatzResearch.WordTrace]
  refine ⟨14572835852869073494969295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 155443582430603450613005813 14572835852869073494969295)
  ·
    refine ⟨21859253779303610242453943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14572835852869073494969295 21859253779303610242453943)
    ·
      refine ⟨32788880668955415363680915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21859253779303610242453943 32788880668955415363680915)
      ·
        refine ⟨49183321003433123045521373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32788880668955415363680915 49183321003433123045521373)
        ·
          refine ⟨18443745376287421142070515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49183321003433123045521373 18443745376287421142070515)
          ·
            refine ⟨27665618064431131713105773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18443745376287421142070515 27665618064431131713105773)
            ·
              refine ⟨10374606774161674392414665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27665618064431131713105773 10374606774161674392414665)
              ·
                refine ⟨7780955080621255794310999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10374606774161674392414665 7780955080621255794310999)
                ·
                  refine ⟨11671432620931883691466499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7780955080621255794310999 11671432620931883691466499)
                  ·
                    refine ⟨17507148931397825537199749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11671432620931883691466499 17507148931397825537199749)
                    ·
                      refine ⟨3282590424637092288224953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17507148931397825537199749 3282590424637092288224953)
                      ·
                        rfl

theorem cell23_6392822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 2, 1, 1, 4].length) (baseStart_6392822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6392822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6392822 prefixEnd_6392822 := by exact prefixLift 6392822
  have htrace : WordTrace (prefixWord ++ tailWord_6392822) baseStart_6392822 baseEnd_6392822 := by
    simpa [prefixWord, tailWord_6392822, baseEnd_6392822] using wordTrace_append hprefix tailTrace_6392822
  have hstable : (prefixWord ++ tailWord_6392822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6392822).length < 2 ^ (prefixWord ++ tailWord_6392822).sum := by decide
  have hdescent : baseEnd_6392822 < baseStart_6392822 := by decide
  rcases family_descends (prefixWord ++ tailWord_6392822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6392839 : List Nat := [1, 1, 4, 3, 1, 1, 2, 5, 1, 2, 2]
def baseStart_6392839 : Nat := 118140960795 + 6392839 * 2 ^ 59
def prefixEnd_6392839 : Nat := 4983230072969 + 3 ^ 40 * 6392839 * 2
def baseEnd_6392839 : Nat := 3282599153808218721712375

theorem tailTrace_6392839 : CollatzResearch.WordTrace tailWord_6392839 prefixEnd_6392839 3282599153808218721712375 := by
  unfold tailWord_6392839
  simp only [CollatzResearch.WordTrace]
  refine ⟨233165993686843587822877571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155443995791229058548585047 233165993686843587822877571)
  ·
    refine ⟨349748990530265381734316357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233165993686843587822877571 349748990530265381734316357)
    ·
      refine ⟨65577935724424759075184317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 349748990530265381734316357 65577935724424759075184317)
      ·
        refine ⟨24591725896659284653194119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65577935724424759075184317 24591725896659284653194119)
        ·
          refine ⟨36887588844988926979791179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24591725896659284653194119 36887588844988926979791179)
          ·
            refine ⟨55331383267483390469686769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36887588844988926979791179 55331383267483390469686769)
            ·
              refine ⟨41498537450612542852265077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55331383267483390469686769 41498537450612542852265077)
              ·
                refine ⟨3890487885994925892399851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41498537450612542852265077 3890487885994925892399851)
                ·
                  refine ⟨5835731828992388838599777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3890487885994925892399851 5835731828992388838599777)
                  ·
                    refine ⟨4376798871744291628949833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5835731828992388838599777 4376798871744291628949833)
                    ·
                      refine ⟨3282599153808218721712375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4376798871744291628949833 3282599153808218721712375)
                      ·
                        rfl

theorem cell23_6392839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_6392839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6392839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6392839 prefixEnd_6392839 := by exact prefixLift 6392839
  have htrace : WordTrace (prefixWord ++ tailWord_6392839) baseStart_6392839 baseEnd_6392839 := by
    simpa [prefixWord, tailWord_6392839, baseEnd_6392839] using wordTrace_append hprefix tailTrace_6392839
  have hstable : (prefixWord ++ tailWord_6392839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6392839).length < 2 ^ (prefixWord ++ tailWord_6392839).sum := by decide
  have hdescent : baseEnd_6392839 < baseStart_6392839 := by decide
  rcases family_descends (prefixWord ++ tailWord_6392839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6392841 : List Nat := [1, 2, 1, 1, 3, 1, 1, 2, 4, 7]
def baseStart_6392841 : Nat := 118140960795 + 6392841 * 2 ^ 59
def prefixEnd_6392841 : Nat := 4983230072969 + 3 ^ 40 * 6392841 * 2
def baseEnd_6392841 : Nat := 1094200060256509237962455

theorem tailTrace_6392841 : CollatzResearch.WordTrace tailWord_6392841 prefixEnd_6392841 1094200060256509237962455 := by
  unfold tailWord_6392841
  simp only [CollatzResearch.WordTrace]
  refine ⟨233166066632836342164450377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155444044421890894776300251 233166066632836342164450377)
  ·
    refine ⟨174874549974627256623337783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233166066632836342164450377 174874549974627256623337783)
    ·
      refine ⟨262311824961940884935006675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174874549974627256623337783 262311824961940884935006675)
      ·
        refine ⟨393467737442911327402510013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262311824961940884935006675 393467737442911327402510013)
        ·
          refine ⟨147550401541091747775941255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 393467737442911327402510013 147550401541091747775941255)
          ·
            refine ⟨221325602311637621663911883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147550401541091747775941255 221325602311637621663911883)
            ·
              refine ⟨331988403467456432495867825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221325602311637621663911883 331988403467456432495867825)
              ·
                refine ⟨248991302600592324371900869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 331988403467456432495867825 248991302600592324371900869)
                ·
                  refine ⟨46685869237611060819731413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 248991302600592324371900869 46685869237611060819731413)
                  ·
                    refine ⟨1094200060256509237962455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46685869237611060819731413 1094200060256509237962455)
                    ·
                      rfl

theorem cell23_6392841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 7].length) (baseStart_6392841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6392841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6392841 prefixEnd_6392841 := by exact prefixLift 6392841
  have htrace : WordTrace (prefixWord ++ tailWord_6392841) baseStart_6392841 baseEnd_6392841 := by
    simpa [prefixWord, tailWord_6392841, baseEnd_6392841] using wordTrace_append hprefix tailTrace_6392841
  have hstable : (prefixWord ++ tailWord_6392841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6392841).length < 2 ^ (prefixWord ++ tailWord_6392841).sum := by decide
  have hdescent : baseEnd_6392841 < baseStart_6392841 := by decide
  rcases family_descends (prefixWord ++ tailWord_6392841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6392856 : List Nat := [2, 1, 2, 3, 2, 2, 4, 2, 1, 2, 2]
def baseStart_6392856 : Nat := 118140960795 + 6392856 * 2 ^ 59
def prefixEnd_6392856 : Nat := 4983230072969 + 3 ^ 40 * 6392856 * 2
def baseEnd_6392856 : Nat := 3282607882979345155199797

theorem tailTrace_6392856 : CollatzResearch.WordTrace tailWord_6392856 prefixEnd_6392856 3282607882979345155199797 := by
  unfold tailWord_6392856
  simp only [CollatzResearch.WordTrace]
  refine ⟨116583306863890999863123211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155444409151854666484164281 116583306863890999863123211)
  ·
    refine ⟨174874960295836499794684817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116583306863890999863123211 174874960295836499794684817)
    ·
      refine ⟨131156220221877374846013613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174874960295836499794684817 131156220221877374846013613)
      ·
        refine ⟨49183582583204015567255105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131156220221877374846013613 49183582583204015567255105)
        ·
          refine ⟨36887686937403011675441329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49183582583204015567255105 36887686937403011675441329)
          ·
            refine ⟨27665765203052258756580997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36887686937403011675441329 27665765203052258756580997)
            ·
              refine ⟨5187330975572298516858937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27665765203052258756580997 5187330975572298516858937)
              ·
                refine ⟨3890498231679223887644203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5187330975572298516858937 3890498231679223887644203)
                ·
                  refine ⟨5835747347518835831466305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3890498231679223887644203 5835747347518835831466305)
                  ·
                    refine ⟨4376810510639126873599729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5835747347518835831466305 4376810510639126873599729)
                    ·
                      refine ⟨3282607882979345155199797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4376810510639126873599729 3282607882979345155199797)
                      ·
                        rfl

theorem cell23_6392856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4, 2, 1, 2, 2].length) (baseStart_6392856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6392856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6392856 prefixEnd_6392856 := by exact prefixLift 6392856
  have htrace : WordTrace (prefixWord ++ tailWord_6392856) baseStart_6392856 baseEnd_6392856 := by
    simpa [prefixWord, tailWord_6392856, baseEnd_6392856] using wordTrace_append hprefix tailTrace_6392856
  have hstable : (prefixWord ++ tailWord_6392856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6392856).length < 2 ^ (prefixWord ++ tailWord_6392856).sum := by decide
  have hdescent : baseEnd_6392856 < baseStart_6392856 := by decide
  rcases family_descends (prefixWord ++ tailWord_6392856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6392882 : List Nat := [3, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2]
def baseStart_6392882 : Nat := 118140960795 + 6392882 * 2 ^ 59
def prefixEnd_6392882 : Nat := 4983230072969 + 3 ^ 40 * 6392882 * 2
def baseEnd_6392882 : Nat := 3282621233476362053474677

theorem tailTrace_6392882 : CollatzResearch.WordTrace tailWord_6392882 prefixEnd_6392882 3282621233476362053474677 := by
  unfold tailWord_6392882
  simp only [CollatzResearch.WordTrace]
  refine ⟨58291890506421951541673225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155445041350458537444461933 58291890506421951541673225)
  ·
    refine ⟨43718917879816463656254919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58291890506421951541673225 43718917879816463656254919)
    ·
      refine ⟨65578376819724695484382379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43718917879816463656254919 65578376819724695484382379)
      ·
        refine ⟨98367565229587043226573569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65578376819724695484382379 98367565229587043226573569)
        ·
          refine ⟨73775673922190282419930177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98367565229587043226573569 73775673922190282419930177)
          ·
            refine ⟨55331755441642711814947633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73775673922190282419930177 55331755441642711814947633)
            ·
              refine ⟨41498816581232033861210725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55331755441642711814947633 41498816581232033861210725)
              ·
                refine ⟨7781028108981006348977011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41498816581232033861210725 7781028108981006348977011)
                ·
                  refine ⟨11671542163471509523465517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7781028108981006348977011 11671542163471509523465517)
                  ·
                    refine ⟨4376828311301816071299569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11671542163471509523465517 4376828311301816071299569)
                    ·
                      refine ⟨3282621233476362053474677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4376828311301816071299569 3282621233476362053474677)
                      ·
                        rfl

theorem cell23_6392882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2].length) (baseStart_6392882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6392882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6392882 prefixEnd_6392882 := by exact prefixLift 6392882
  have htrace : WordTrace (prefixWord ++ tailWord_6392882) baseStart_6392882 baseEnd_6392882 := by
    simpa [prefixWord, tailWord_6392882, baseEnd_6392882] using wordTrace_append hprefix tailTrace_6392882
  have hstable : (prefixWord ++ tailWord_6392882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6392882).length < 2 ^ (prefixWord ++ tailWord_6392882).sum := by decide
  have hdescent : baseEnd_6392882 < baseStart_6392882 := by decide
  rcases family_descends (prefixWord ++ tailWord_6392882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6392995 : List Nat := [1, 1, 1, 4, 1, 1, 1, 6, 3, 4]
def baseStart_6392995 : Nat := 118140960795 + 6392995 * 2 ^ 59
def prefixEnd_6392995 : Nat := 4983230072969 + 3 ^ 40 * 6392995 * 2
def baseEnd_6392995 : Nat := 1094226418930106703787219

theorem tailTrace_6392995 : CollatzResearch.WordTrace tailWord_6392995 prefixEnd_6392995 1094226418930106703787219 := by
  unfold tailWord_6392995
  simp only [CollatzResearch.WordTrace]
  refine ⟨233171683474278426465556439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155447788982852284310370959 233171683474278426465556439)
  ·
    refine ⟨349757525211417639698334659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233171683474278426465556439 349757525211417639698334659)
    ·
      refine ⟨524636287817126459547501989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349757525211417639698334659 524636287817126459547501989)
      ·
        refine ⟨98369303965711211165156623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 524636287817126459547501989 98369303965711211165156623)
        ·
          refine ⟨147553955948566816747734935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98369303965711211165156623 147553955948566816747734935)
          ·
            refine ⟨221330933922850225121602403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147553955948566816747734935 221330933922850225121602403)
            ·
              refine ⟨331996400884275337682403605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221330933922850225121602403 331996400884275337682403605)
              ·
                refine ⟨15562331291450406453862669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 331996400884275337682403605 15562331291450406453862669)
                ·
                  refine ⟨5835874234293902420198501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15562331291450406453862669 5835874234293902420198501)
                  ·
                    refine ⟨1094226418930106703787219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5835874234293902420198501 1094226418930106703787219)
                    ·
                      rfl

theorem cell23_6392995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6, 3, 4].length) (baseStart_6392995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6392995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6392995 prefixEnd_6392995 := by exact prefixLift 6392995
  have htrace : WordTrace (prefixWord ++ tailWord_6392995) baseStart_6392995 baseEnd_6392995 := by
    simpa [prefixWord, tailWord_6392995, baseEnd_6392995] using wordTrace_append hprefix tailTrace_6392995
  have hstable : (prefixWord ++ tailWord_6392995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6392995).length < 2 ^ (prefixWord ++ tailWord_6392995).sum := by decide
  have hdescent : baseEnd_6392995 < baseStart_6392995 := by decide
  rcases family_descends (prefixWord ++ tailWord_6392995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6393046 : List Nat := [5, 2, 1, 2, 2, 1, 1, 2, 3, 4]
def baseStart_6393046 : Nat := 118140960795 + 6393046 * 2 ^ 59
def prefixEnd_6393046 : Nat := 4983230072969 + 3 ^ 40 * 6393046 * 2
def baseEnd_6393046 : Nat := 1094235148101233137274641

theorem tailTrace_6393046 : CollatzResearch.WordTrace tailWord_6393046 prefixEnd_6393046 1094235148101233137274641 := by
  unfold tailWord_6393046
  simp only [CollatzResearch.WordTrace]
  refine ⟨14573346474818353885978937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 155449029064729108117108661 14573346474818353885978937)
  ·
    refine ⟨10930009856113765414484203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14573346474818353885978937 10930009856113765414484203)
    ·
      refine ⟨16395014784170648121726305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10930009856113765414484203 16395014784170648121726305)
      ·
        refine ⟨12296261088127986091294729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16395014784170648121726305 12296261088127986091294729)
        ·
          refine ⟨9222195816095989568471047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12296261088127986091294729 9222195816095989568471047)
          ·
            refine ⟨13833293724143984352706571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9222195816095989568471047 13833293724143984352706571)
            ·
              refine ⟨20749940586215976529059857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13833293724143984352706571 20749940586215976529059857)
              ·
                refine ⟨15562455439661982396794893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20749940586215976529059857 15562455439661982396794893)
                ·
                  refine ⟨5835920789873243398798085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15562455439661982396794893 5835920789873243398798085)
                  ·
                    refine ⟨1094235148101233137274641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5835920789873243398798085 1094235148101233137274641)
                    ·
                      rfl

theorem cell23_6393046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_6393046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6393046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6393046 prefixEnd_6393046 := by exact prefixLift 6393046
  have htrace : WordTrace (prefixWord ++ tailWord_6393046) baseStart_6393046 baseEnd_6393046 := by
    simpa [prefixWord, tailWord_6393046, baseEnd_6393046] using wordTrace_append hprefix tailTrace_6393046
  have hstable : (prefixWord ++ tailWord_6393046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6393046).length < 2 ^ (prefixWord ++ tailWord_6393046).sum := by decide
  have hdescent : baseEnd_6393046 < baseStart_6393046 := by decide
  rcases family_descends (prefixWord ++ tailWord_6393046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6393055 : List Nat := [1, 1, 2, 3, 2, 1, 4, 1, 3, 5]
def baseStart_6393055 : Nat := 118140960795 + 6393055 * 2 ^ 59
def prefixEnd_6393055 : Nat := 4983230072969 + 3 ^ 40 * 6393055 * 2
def baseEnd_6393055 : Nat := 1094236688543196625537127

theorem tailTrace_6393055 : CollatzResearch.WordTrace tailWord_6393055 prefixEnd_6393055 1094236688543196625537127 := by
  unfold tailWord_6393055
  simp only [CollatzResearch.WordTrace]
  refine ⟨233173871854061056712740619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155449247902707371141827079 233173871854061056712740619)
  ·
    refine ⟨349760807781091585069110929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233173871854061056712740619 349760807781091585069110929)
    ·
      refine ⟨262320605835818688801833197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 349760807781091585069110929 262320605835818688801833197)
      ·
        refine ⟨98370227188432008300687449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 262320605835818688801833197 98370227188432008300687449)
        ·
          refine ⟨73777670391324006225515587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98370227188432008300687449 73777670391324006225515587)
          ·
            refine ⟨110666505586986009338273381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73777670391324006225515587 110666505586986009338273381)
            ·
              refine ⟨20749969797559876750926259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110666505586986009338273381 20749969797559876750926259)
              ·
                refine ⟨31124954696339815126389389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20749969797559876750926259 31124954696339815126389389)
                ·
                  refine ⟨11671858011127430672396021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31124954696339815126389389 11671858011127430672396021)
                  ·
                    refine ⟨1094236688543196625537127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11671858011127430672396021 1094236688543196625537127)
                    ·
                      rfl

theorem cell23_6393055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 3, 5].length) (baseStart_6393055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6393055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6393055 prefixEnd_6393055 := by exact prefixLift 6393055
  have htrace : WordTrace (prefixWord ++ tailWord_6393055) baseStart_6393055 baseEnd_6393055 := by
    simpa [prefixWord, tailWord_6393055, baseEnd_6393055] using wordTrace_append hprefix tailTrace_6393055
  have hstable : (prefixWord ++ tailWord_6393055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6393055).length < 2 ^ (prefixWord ++ tailWord_6393055).sum := by decide
  have hdescent : baseEnd_6393055 < baseStart_6393055 := by decide
  rcases family_descends (prefixWord ++ tailWord_6393055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6393076 : List Nat := [2, 6, 1, 2, 1, 1, 1, 1, 8]
def baseStart_6393076 : Nat := 118140960795 + 6393076 * 2 ^ 59
def prefixEnd_6393076 : Nat := 4983230072969 + 3 ^ 40 * 6393076 * 2
def baseEnd_6393076 : Nat := 364746760969259366049865

theorem tailTrace_6393076 : CollatzResearch.WordTrace tailWord_6393076 prefixEnd_6393076 364746760969259366049865 := by
  unfold tailWord_6393076
  simp only [CollatzResearch.WordTrace]
  refine ⟨116587318893492488649627541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155449758524656651532836721 116587318893492488649627541)
  ·
    refine ⟨5465030573132460405451291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 116587318893492488649627541 5465030573132460405451291)
    ·
      refine ⟨8197545859698690608176937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5465030573132460405451291 8197545859698690608176937)
      ·
        refine ⟨6148159394774017956132703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8197545859698690608176937 6148159394774017956132703)
        ·
          refine ⟨9222239092161026934199055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6148159394774017956132703 9222239092161026934199055)
          ·
            refine ⟨13833358638241540401298583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9222239092161026934199055 13833358638241540401298583)
            ·
              refine ⟨20750037957362310601947875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13833358638241540401298583 20750037957362310601947875)
              ·
                refine ⟨31125056936043465902921813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20750037957362310601947875 31125056936043465902921813)
                ·
                  refine ⟨364746760969259366049865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31125056936043465902921813 364746760969259366049865)
                  ·
                    rfl

theorem cell23_6393076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_6393076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6393076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6393076 prefixEnd_6393076 := by exact prefixLift 6393076
  have htrace : WordTrace (prefixWord ++ tailWord_6393076) baseStart_6393076 baseEnd_6393076 := by
    simpa [prefixWord, tailWord_6393076, baseEnd_6393076] using wordTrace_append hprefix tailTrace_6393076
  have hstable : (prefixWord ++ tailWord_6393076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6393076).length < 2 ^ (prefixWord ++ tailWord_6393076).sum := by decide
  have hdescent : baseEnd_6393076 < baseStart_6393076 := by decide
  rcases family_descends (prefixWord ++ tailWord_6393076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6393086 : List Nat := [4, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3]
def baseStart_6393086 : Nat := 118140960795 + 6393086 * 2 ^ 59
def prefixEnd_6393086 : Nat := 4983230072969 + 3 ^ 40 * 6393086 * 2
def baseEnd_6393086 : Nat := 3282725983529879255323739

theorem tailTrace_6393086 : CollatzResearch.WordTrace tailWord_6393086 prefixEnd_6393086 3282725983529879255323739 := by
  unfold tailWord_6393086
  simp only [CollatzResearch.WordTrace]
  refine ⟨29146875314618593625889889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155450001677965832671412741 29146875314618593625889889)
  ·
    refine ⟨21860156485963945219417417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29146875314618593625889889 21860156485963945219417417)
    ·
      refine ⟨16395117364472958914563063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21860156485963945219417417 16395117364472958914563063)
      ·
        refine ⟨24592676046709438371844595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16395117364472958914563063 24592676046709438371844595)
        ·
          refine ⟨36889014070064157557766893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24592676046709438371844595 36889014070064157557766893)
          ·
            refine ⟨13833380276274059084162585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36889014070064157557766893 13833380276274059084162585)
            ·
              refine ⟨10375035207205544313121939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13833380276274059084162585 10375035207205544313121939)
              ·
                refine ⟨15562552810808316469682909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10375035207205544313121939 15562552810808316469682909)
                ·
                  refine ⟨5835957304053118676131091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15562552810808316469682909 5835957304053118676131091)
                  ·
                    refine ⟨8753935956079678014196637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5835957304053118676131091 8753935956079678014196637)
                    ·
                      refine ⟨3282725983529879255323739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8753935956079678014196637 3282725983529879255323739)
                      ·
                        rfl

theorem cell23_6393086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_6393086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6393086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6393086 prefixEnd_6393086 := by exact prefixLift 6393086
  have htrace : WordTrace (prefixWord ++ tailWord_6393086) baseStart_6393086 baseEnd_6393086 := by
    simpa [prefixWord, tailWord_6393086, baseEnd_6393086] using wordTrace_append hprefix tailTrace_6393086
  have hstable : (prefixWord ++ tailWord_6393086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6393086).length < 2 ^ (prefixWord ++ tailWord_6393086).sum := by decide
  have hdescent : baseEnd_6393086 < baseStart_6393086 := by decide
  rcases family_descends (prefixWord ++ tailWord_6393086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6393102 : List Nat := [4, 1, 1, 2, 1, 3, 3, 1, 1, 6]
def baseStart_6393102 : Nat := 118140960795 + 6393102 * 2 ^ 59
def prefixEnd_6393102 : Nat := 4983230072969 + 3 ^ 40 * 6393102 * 2
def baseEnd_6393102 : Nat := 1094244733073450397574555

theorem tailTrace_6393102 : CollatzResearch.WordTrace tailWord_6393102 prefixEnd_6393102 1094244733073450397574555 := by
  unfold tailWord_6393102
  simp only [CollatzResearch.WordTrace]
  refine ⟨29146948260611347967462695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155450390723260522493134373 29146948260611347967462695)
  ·
    refine ⟨43720422390917021951194043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29146948260611347967462695 43720422390917021951194043)
    ·
      refine ⟨65580633586375532926791065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43720422390917021951194043 65580633586375532926791065)
      ·
        refine ⟨49185475189781649695093299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65580633586375532926791065 49185475189781649695093299)
        ·
          refine ⟨73778212784672474542639949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49185475189781649695093299 73778212784672474542639949)
          ·
            refine ⟨27666829794252177953489981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73778212784672474542639949 27666829794252177953489981)
            ·
              refine ⟨10375061172844566732558743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27666829794252177953489981 10375061172844566732558743)
              ·
                refine ⟨15562591759266850098838115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10375061172844566732558743 15562591759266850098838115)
                ·
                  refine ⟨23343887638900275148257173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15562591759266850098838115 23343887638900275148257173)
                  ·
                    refine ⟨1094244733073450397574555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23343887638900275148257173 1094244733073450397574555)
                    ·
                      rfl

theorem cell23_6393102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 1, 1, 6].length) (baseStart_6393102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6393102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6393102 prefixEnd_6393102 := by exact prefixLift 6393102
  have htrace : WordTrace (prefixWord ++ tailWord_6393102) baseStart_6393102 baseEnd_6393102 := by
    simpa [prefixWord, tailWord_6393102, baseEnd_6393102] using wordTrace_append hprefix tailTrace_6393102
  have hstable : (prefixWord ++ tailWord_6393102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6393102).length < 2 ^ (prefixWord ++ tailWord_6393102).sum := by decide
  have hdescent : baseEnd_6393102 < baseStart_6393102 := by decide
  rcases family_descends (prefixWord ++ tailWord_6393102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6393105 : List Nat := [1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 6]
def baseStart_6393105 : Nat := 118140960795 + 6393105 * 2 ^ 59
def prefixEnd_6393105 : Nat := 4983230072969 + 3 ^ 40 * 6393105 * 2
def baseEnd_6393105 : Nat := 3282735739662314680986151

theorem tailTrace_6393105 : CollatzResearch.WordTrace tailWord_6393105 prefixEnd_6393105 3282735739662314680986151 := by
  unfold tailWord_6393105
  simp only [CollatzResearch.WordTrace]
  refine ⟨233175695503879915252060769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155450463669253276834707179 233175695503879915252060769)
  ·
    refine ⟨174881771627909936439045577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233175695503879915252060769 174881771627909936439045577)
    ·
      refine ⟨131161328720932452329284183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174881771627909936439045577 131161328720932452329284183)
      ·
        refine ⟨196741993081398678493926275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131161328720932452329284183 196741993081398678493926275)
        ·
          refine ⟨295112989622098017740889413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196741993081398678493926275 295112989622098017740889413)
          ·
            refine ⟨55333685554143378326416765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 295112989622098017740889413 55333685554143378326416765)
            ·
              refine ⟨20750132082803766872406287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55333685554143378326416765 20750132082803766872406287)
              ·
                refine ⟨31125198124205650308609431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20750132082803766872406287 31125198124205650308609431)
                ·
                  refine ⟨46687797186308475462914147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31125198124205650308609431 46687797186308475462914147)
                  ·
                    refine ⟨70031695779462713194371221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46687797186308475462914147 70031695779462713194371221)
                    ·
                      refine ⟨3282735739662314680986151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70031695779462713194371221 3282735739662314680986151)
                      ·
                        rfl

theorem cell23_6393105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 6].length) (baseStart_6393105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6393105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6393105 prefixEnd_6393105 := by exact prefixLift 6393105
  have htrace : WordTrace (prefixWord ++ tailWord_6393105) baseStart_6393105 baseEnd_6393105 := by
    simpa [prefixWord, tailWord_6393105, baseEnd_6393105] using wordTrace_append hprefix tailTrace_6393105
  have hstable : (prefixWord ++ tailWord_6393105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6393105).length < 2 ^ (prefixWord ++ tailWord_6393105).sum := by decide
  have hdescent : baseEnd_6393105 < baseStart_6393105 := by decide
  rcases family_descends (prefixWord ++ tailWord_6393105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6393120 : List Nat := [2, 1, 1, 5, 4, 1, 1, 3, 1, 1, 3]
def baseStart_6393120 : Nat := 118140960795 + 6393120 * 2 ^ 59
def prefixEnd_6393120 : Nat := 4983230072969 + 3 ^ 40 * 6393120 * 2
def baseEnd_6393120 : Nat := 3282743441872132122298583

theorem tailTrace_6393120 : CollatzResearch.WordTrace tailWord_6393120 prefixEnd_6393120 3282743441872132122298583 := by
  unfold tailWord_6393120
  simp only [CollatzResearch.WordTrace]
  refine ⟨116588121299412786406928407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155450828399217048542571209 116588121299412786406928407)
  ·
    refine ⟨174882181949119179610392611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116588121299412786406928407 174882181949119179610392611)
    ·
      refine ⟨262323272923678769415588917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174882181949119179610392611 262323272923678769415588917)
      ·
        refine ⟨24592806836594884632711461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 262323272923678769415588917 24592806836594884632711461)
        ·
          refine ⟨4611151281861540868633399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24592806836594884632711461 4611151281861540868633399)
          ·
            refine ⟨6916726922792311302950099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4611151281861540868633399 6916726922792311302950099)
            ·
              refine ⟨10375090384188466954425149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6916726922792311302950099 10375090384188466954425149)
              ·
                refine ⟨3890658894070675107909431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10375090384188466954425149 3890658894070675107909431)
                ·
                  refine ⟨5835988341106012661864147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3890658894070675107909431 5835988341106012661864147)
                  ·
                    refine ⟨8753982511659018992796221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5835988341106012661864147 8753982511659018992796221)
                    ·
                      refine ⟨3282743441872132122298583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8753982511659018992796221 3282743441872132122298583)
                      ·
                        rfl

theorem cell23_6393120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_6393120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6393120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6393120 prefixEnd_6393120 := by exact prefixLift 6393120
  have htrace : WordTrace (prefixWord ++ tailWord_6393120) baseStart_6393120 baseEnd_6393120 := by
    simpa [prefixWord, tailWord_6393120, baseEnd_6393120] using wordTrace_append hprefix tailTrace_6393120
  have hstable : (prefixWord ++ tailWord_6393120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6393120).length < 2 ^ (prefixWord ++ tailWord_6393120).sum := by decide
  have hdescent : baseEnd_6393120 < baseStart_6393120 := by decide
  rcases family_descends (prefixWord ++ tailWord_6393120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6393149 : List Nat := [1, 4, 1, 5, 1, 1, 2, 8]
def baseStart_6393149 : Nat := 118140960795 + 6393149 * 2 ^ 59
def prefixEnd_6393149 : Nat := 4983230072969 + 3 ^ 40 * 6393149 * 2
def baseEnd_6393149 : Nat := 121583641955967129956887

theorem tailTrace_6393149 : CollatzResearch.WordTrace tailWord_6393149 prefixEnd_6393149 121583641955967129956887 := by
  unfold tailWord_6393149
  simp only [CollatzResearch.WordTrace]
  refine ⟨233177300315720510766662501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155451533543813673844441667 233177300315720510766662501)
  ·
    refine ⟨43720743809197595768749219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 233177300315720510766662501 43720743809197595768749219)
    ·
      refine ⟨65581115713796393653123829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43720743809197595768749219 65581115713796393653123829)
      ·
        refine ⟨6148229598168411904980359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65581115713796393653123829 6148229598168411904980359)
        ·
          refine ⟨9222344397252617857470539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6148229598168411904980359 9222344397252617857470539)
          ·
            refine ⟨13833516595878926786205809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9222344397252617857470539 13833516595878926786205809)
            ·
              refine ⟨10375137446909195089654357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13833516595878926786205809 10375137446909195089654357)
              ·
                refine ⟨121583641955967129956887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10375137446909195089654357 121583641955967129956887)
                ·
                  rfl

theorem cell23_6393149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 8].length) (baseStart_6393149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6393149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6393149 prefixEnd_6393149 := by exact prefixLift 6393149
  have htrace : WordTrace (prefixWord ++ tailWord_6393149) baseStart_6393149 baseEnd_6393149 := by
    simpa [prefixWord, tailWord_6393149, baseEnd_6393149] using wordTrace_append hprefix tailTrace_6393149
  have hstable : (prefixWord ++ tailWord_6393149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6393149).length < 2 ^ (prefixWord ++ tailWord_6393149).sum := by decide
  have hdescent : baseEnd_6393149 < baseStart_6393149 := by decide
  rcases family_descends (prefixWord ++ tailWord_6393149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6393153 : List Nat := [1, 2, 5, 2, 1, 3, 2, 1, 2, 4]
def baseStart_6393153 : Nat := 118140960795 + 6393153 * 2 ^ 59
def prefixEnd_6393153 : Nat := 4983230072969 + 3 ^ 40 * 6393153 * 2
def baseEnd_6393153 : Nat := 1094253462244576831061977

theorem tailTrace_6393153 : CollatzResearch.WordTrace tailWord_6393153 prefixEnd_6393153 1094253462244576831061977 := by
  unfold tailWord_6393153
  simp only [CollatzResearch.WordTrace]
  refine ⟨233177446207706019449808113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155451630805137346299872075 233177446207706019449808113)
  ·
    refine ⟨174883084655779514587356085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233177446207706019449808113 174883084655779514587356085)
    ·
      refine ⟨16395289186479329492564633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 174883084655779514587356085 16395289186479329492564633)
      ·
        refine ⟨12296466889859497119423475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16395289186479329492564633 12296466889859497119423475)
        ·
          refine ⟨18444700334789245679135213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12296466889859497119423475 18444700334789245679135213)
          ·
            refine ⟨6916762625545967129675705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18444700334789245679135213 6916762625545967129675705)
            ·
              refine ⟨5187571969159475347256779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6916762625545967129675705 5187571969159475347256779)
              ·
                refine ⟨7781357953739213020885169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5187571969159475347256779 7781357953739213020885169)
                ·
                  refine ⟨5836018465304409765663877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7781357953739213020885169 5836018465304409765663877)
                  ·
                    refine ⟨1094253462244576831061977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5836018465304409765663877 1094253462244576831061977)
                    ·
                      rfl

theorem cell23_6393153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_6393153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6393153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6393153 prefixEnd_6393153 := by exact prefixLift 6393153
  have htrace : WordTrace (prefixWord ++ tailWord_6393153) baseStart_6393153 baseEnd_6393153 := by
    simpa [prefixWord, tailWord_6393153, baseEnd_6393153] using wordTrace_append hprefix tailTrace_6393153
  have hstable : (prefixWord ++ tailWord_6393153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6393153).length < 2 ^ (prefixWord ++ tailWord_6393153).sum := by decide
  have hdescent : baseEnd_6393153 < baseStart_6393153 := by decide
  rcases family_descends (prefixWord ++ tailWord_6393153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6393169 : List Nat := [1, 2, 2, 1, 4, 1, 3, 1, 3, 3, 2]
def baseStart_6393169 : Nat := 118140960795 + 6393169 * 2 ^ 59
def prefixEnd_6393169 : Nat := 4983230072969 + 3 ^ 40 * 6393169 * 2
def baseEnd_6393169 : Nat := 3282768602424202430585857

theorem tailTrace_6393169 : CollatzResearch.WordTrace tailWord_6393169 prefixEnd_6393169 3282768602424202430585857 := by
  unfold tailWord_6393169
  simp only [CollatzResearch.WordTrace]
  refine ⟨233178029775648054182390561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155452019850432036121593707 233178029775648054182390561)
  ·
    refine ⟨174883522331736040636792921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233178029775648054182390561 174883522331736040636792921)
    ·
      refine ⟨131162641748802030477594691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174883522331736040636792921 131162641748802030477594691)
      ·
        refine ⟨196743962623203045716392037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131162641748802030477594691 196743962623203045716392037)
        ·
          refine ⟨36889492991850571071823507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 196743962623203045716392037 36889492991850571071823507)
          ·
            refine ⟨55334239487775856607735261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36889492991850571071823507 55334239487775856607735261)
            ·
              refine ⟨20750339807915946227900723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55334239487775856607735261 20750339807915946227900723)
              ·
                refine ⟨31125509711873919341851085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20750339807915946227900723 31125509711873919341851085)
                ·
                  refine ⟨11672066141952719753194157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31125509711873919341851085 11672066141952719753194157)
                  ·
                    refine ⟨4377024803232269907447809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11672066141952719753194157 4377024803232269907447809)
                    ·
                      refine ⟨3282768602424202430585857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4377024803232269907447809 3282768602424202430585857)
                      ·
                        rfl

theorem cell23_6393169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 3, 3, 2].length) (baseStart_6393169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6393169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6393169 prefixEnd_6393169 := by exact prefixLift 6393169
  have htrace : WordTrace (prefixWord ++ tailWord_6393169) baseStart_6393169 baseEnd_6393169 := by
    simpa [prefixWord, tailWord_6393169, baseEnd_6393169] using wordTrace_append hprefix tailTrace_6393169
  have hstable : (prefixWord ++ tailWord_6393169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6393169).length < 2 ^ (prefixWord ++ tailWord_6393169).sum := by decide
  have hdescent : baseEnd_6393169 < baseStart_6393169 := by decide
  rcases family_descends (prefixWord ++ tailWord_6393169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6393194 : List Nat := [3, 1, 3, 3, 3, 1, 2, 2, 1, 2, 2]
def baseStart_6393194 : Nat := 118140960795 + 6393194 * 2 ^ 59
def prefixEnd_6393194 : Nat := 4983230072969 + 3 ^ 40 * 6393194 * 2
def baseEnd_6393194 : Nat := 3282781439440564832773243

theorem tailTrace_6393194 : CollatzResearch.WordTrace tailWord_6393194 prefixEnd_6393194 3282781439440564832773243 := by
  unfold tailWord_6393194
  simp only [CollatzResearch.WordTrace]
  refine ⟨58294735400139370863012659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155452627733704988968033757 58294735400139370863012659)
  ·
    refine ⟨87442103100209056294518989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58294735400139370863012659 87442103100209056294518989)
    ·
      refine ⟨32790788662578396110444621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87442103100209056294518989 32790788662578396110444621)
      ·
        refine ⟨12296545748466898541416733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32790788662578396110444621 12296545748466898541416733)
        ·
          refine ⟨4611204655675086953031275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12296545748466898541416733 4611204655675086953031275)
          ·
            refine ⟨6916806983512630429546913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4611204655675086953031275 6916806983512630429546913)
            ·
              refine ⟨5187605237634472822160185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6916806983512630429546913 5187605237634472822160185)
              ·
                refine ⟨3890703928225854616620139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5187605237634472822160185 3890703928225854616620139)
                ·
                  refine ⟨5836055892338781924930209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3890703928225854616620139 5836055892338781924930209)
                  ·
                    refine ⟨4377041919254086443697657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5836055892338781924930209 4377041919254086443697657)
                    ·
                      refine ⟨3282781439440564832773243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4377041919254086443697657 3282781439440564832773243)
                      ·
                        rfl

theorem cell23_6393194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_6393194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6393194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6393194 prefixEnd_6393194 := by exact prefixLift 6393194
  have htrace : WordTrace (prefixWord ++ tailWord_6393194) baseStart_6393194 baseEnd_6393194 := by
    simpa [prefixWord, tailWord_6393194, baseEnd_6393194] using wordTrace_append hprefix tailTrace_6393194
  have hstable : (prefixWord ++ tailWord_6393194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6393194).length < 2 ^ (prefixWord ++ tailWord_6393194).sum := by decide
  have hdescent : baseEnd_6393194 < baseStart_6393194 := by decide
  rcases family_descends (prefixWord ++ tailWord_6393194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6393202 : List Nat := [3, 2, 1, 2, 1, 2, 1, 1, 1, 6, 3]
def baseStart_6393202 : Nat := 118140960795 + 6393202 * 2 ^ 59
def prefixEnd_6393202 : Nat := 4983230072969 + 3 ^ 40 * 6393202 * 2
def baseEnd_6393202 : Nat := 3282785547285800801473205

theorem tailTrace_6393202 : CollatzResearch.WordTrace tailWord_6393202 prefixEnd_6393202 3282785547285800801473205 := by
  unfold tailWord_6393202
  simp only [CollatzResearch.WordTrace]
  refine ⟨58294808346132125204585465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155452822256352333878894573 58294808346132125204585465)
  ·
    refine ⟨43721106259599093903439099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58294808346132125204585465 43721106259599093903439099)
    ·
      refine ⟨65581659389398640855158649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43721106259599093903439099 65581659389398640855158649)
      ·
        refine ⟨49186244542048980641368987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65581659389398640855158649 49186244542048980641368987)
        ·
          refine ⟨73779366813073470962053481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49186244542048980641368987 73779366813073470962053481)
          ·
            refine ⟨55334525109805103221540111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73779366813073470962053481 55334525109805103221540111)
            ·
              refine ⟨83001787664707654832310167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55334525109805103221540111 83001787664707654832310167)
              ·
                refine ⟨124502681497061482248465251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83001787664707654832310167 124502681497061482248465251)
                ·
                  refine ⟨186754022245592223372697877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124502681497061482248465251 186754022245592223372697877)
                  ·
                    refine ⟨8754094792762135470595213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 186754022245592223372697877 8754094792762135470595213)
                    ·
                      refine ⟨3282785547285800801473205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8754094792762135470595213 3282785547285800801473205)
                      ·
                        rfl

theorem cell23_6393202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_6393202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6393202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6393202 prefixEnd_6393202 := by exact prefixLift 6393202
  have htrace : WordTrace (prefixWord ++ tailWord_6393202) baseStart_6393202 baseEnd_6393202 := by
    simpa [prefixWord, tailWord_6393202, baseEnd_6393202] using wordTrace_append hprefix tailTrace_6393202
  have hstable : (prefixWord ++ tailWord_6393202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6393202).length < 2 ^ (prefixWord ++ tailWord_6393202).sum := by decide
  have hdescent : baseEnd_6393202 < baseStart_6393202 := by decide
  rcases family_descends (prefixWord ++ tailWord_6393202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6393212 : List Nat := [2, 2, 2, 1, 1, 1, 5, 1, 2, 2, 4]
def baseStart_6393212 : Nat := 118140960795 + 6393212 * 2 ^ 59
def prefixEnd_6393212 : Nat := 4983230072969 + 3 ^ 40 * 6393212 * 2
def baseEnd_6393212 : Nat := 3282790682092345762348159

theorem tailTrace_6393212 : CollatzResearch.WordTrace tailWord_6393212 prefixEnd_6393212 3282790682092345762348159 := by
  unfold tailWord_6393212
  simp only [CollatzResearch.WordTrace]
  refine ⟨116589799057246136263102945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155453065409661515017470593 116589799057246136263102945)
  ·
    refine ⟨87442349292934602197327209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116589799057246136263102945 87442349292934602197327209)
    ·
      refine ⟨65581761969700951647995407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87442349292934602197327209 65581761969700951647995407)
      ·
        refine ⟨98372642954551427471993111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65581761969700951647995407 98372642954551427471993111)
        ·
          refine ⟨147558964431827141207989667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98372642954551427471993111 147558964431827141207989667)
          ·
            refine ⟨221338446647740711811984501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147558964431827141207989667 221338446647740711811984501)
            ·
              refine ⟨20750479373225691732373547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 221338446647740711811984501 20750479373225691732373547)
              ·
                refine ⟨31125719059838537598560321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20750479373225691732373547 31125719059838537598560321)
                ·
                  refine ⟨23344289294878903198920241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31125719059838537598560321 23344289294878903198920241)
                  ·
                    refine ⟨17508216971159177399190181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23344289294878903198920241 17508216971159177399190181)
                    ·
                      refine ⟨3282790682092345762348159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17508216971159177399190181 3282790682092345762348159)
                      ·
                        rfl

theorem cell23_6393212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_6393212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6393212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6393212 prefixEnd_6393212 := by exact prefixLift 6393212
  have htrace : WordTrace (prefixWord ++ tailWord_6393212) baseStart_6393212 baseEnd_6393212 := by
    simpa [prefixWord, tailWord_6393212, baseEnd_6393212] using wordTrace_append hprefix tailTrace_6393212
  have hstable : (prefixWord ++ tailWord_6393212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6393212).length < 2 ^ (prefixWord ++ tailWord_6393212).sum := by decide
  have hdescent : baseEnd_6393212 < baseStart_6393212 := by decide
  rcases family_descends (prefixWord ++ tailWord_6393212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6393250 : List Nat := [3, 3, 1, 2, 1, 4, 1, 2, 2, 2, 2]
def baseStart_6393250 : Nat := 118140960795 + 6393250 * 2 ^ 59
def prefixEnd_6393250 : Nat := 4983230072969 + 3 ^ 40 * 6393250 * 2
def baseEnd_6393250 : Nat := 3282810194357216613672985

theorem tailTrace_6393250 : CollatzResearch.WordTrace tailWord_6393250 prefixEnd_6393250 3282810194357216613672985 := by
  unfold tailWord_6393250
  simp only [CollatzResearch.WordTrace]
  refine ⟨58295246022088651254022301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155453989392236403344059469 58295246022088651254022301)
  ·
    refine ⟨21860717258283244220258363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58295246022088651254022301 21860717258283244220258363)
    ·
      refine ⟨32791075887424866330387545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21860717258283244220258363 32791075887424866330387545)
      ·
        refine ⟨24593306915568649747790659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32791075887424866330387545 24593306915568649747790659)
        ·
          refine ⟨36889960373352974621685989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24593306915568649747790659 36889960373352974621685989)
          ·
            refine ⟨6916867570003682741566123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36889960373352974621685989 6916867570003682741566123)
            ·
              refine ⟨10375301355005524112349185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6916867570003682741566123 10375301355005524112349185)
              ·
                refine ⟨7781476016254143084261889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10375301355005524112349185 7781476016254143084261889)
                ·
                  refine ⟨5836107012190607313196417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7781476016254143084261889 5836107012190607313196417)
                  ·
                    refine ⟨4377080259142955484897313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5836107012190607313196417 4377080259142955484897313)
                    ·
                      refine ⟨3282810194357216613672985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4377080259142955484897313 3282810194357216613672985)
                      ·
                        rfl

theorem cell23_6393250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_6393250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6393250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6393250 prefixEnd_6393250 := by exact prefixLift 6393250
  have htrace : WordTrace (prefixWord ++ tailWord_6393250) baseStart_6393250 baseEnd_6393250 := by
    simpa [prefixWord, tailWord_6393250, baseEnd_6393250] using wordTrace_append hprefix tailTrace_6393250
  have hstable : (prefixWord ++ tailWord_6393250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6393250).length < 2 ^ (prefixWord ++ tailWord_6393250).sum := by decide
  have hdescent : baseEnd_6393250 < baseStart_6393250 := by decide
  rcases family_descends (prefixWord ++ tailWord_6393250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6393252 : List Nat := [2, 3, 1, 2, 1, 1, 1, 3, 4, 5]
def baseStart_6393252 : Nat := 118140960795 + 6393252 * 2 ^ 59
def prefixEnd_6393252 : Nat := 4983230072969 + 3 ^ 40 * 6393252 * 2
def baseEnd_6393252 : Nat := 1094270407106175201949325

theorem tailTrace_6393252 : CollatzResearch.WordTrace tailWord_6393252 prefixEnd_6393252 1094270407106175201949325 := by
  unfold tailWord_6393252
  simp only [CollatzResearch.WordTrace]
  refine ⟨116590528517173679678831005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155454038022898239571774673 116590528517173679678831005)
  ·
    refine ⟨43721448193940129879561627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116590528517173679678831005 43721448193940129879561627)
    ·
      refine ⟨65582172290910194819342441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43721448193940129879561627 65582172290910194819342441)
      ·
        refine ⟨49186629218182646114506831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65582172290910194819342441 49186629218182646114506831)
        ·
          refine ⟨73779943827273969171760247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49186629218182646114506831 73779943827273969171760247)
          ·
            refine ⟨110669915740910953757640371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73779943827273969171760247 110669915740910953757640371)
            ·
              refine ⟨166004873611366430636460557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110669915740910953757640371 166004873611366430636460557)
              ·
                refine ⟨62251827604262411488672709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 166004873611366430636460557 62251827604262411488672709)
                ·
                  refine ⟨11672217675799202154126133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62251827604262411488672709 11672217675799202154126133)
                  ·
                    refine ⟨1094270407106175201949325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11672217675799202154126133 1094270407106175201949325)
                    ·
                      rfl

theorem cell23_6393252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 4, 5].length) (baseStart_6393252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6393252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6393252 prefixEnd_6393252 := by exact prefixLift 6393252
  have htrace : WordTrace (prefixWord ++ tailWord_6393252) baseStart_6393252 baseEnd_6393252 := by
    simpa [prefixWord, tailWord_6393252, baseEnd_6393252] using wordTrace_append hprefix tailTrace_6393252
  have hstable : (prefixWord ++ tailWord_6393252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6393252).length < 2 ^ (prefixWord ++ tailWord_6393252).sum := by decide
  have hdescent : baseEnd_6393252 < baseStart_6393252 := by decide
  rcases family_descends (prefixWord ++ tailWord_6393252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6393256 : List Nat := [2, 1, 6, 1, 2, 1, 2, 1, 7]
def baseStart_6393256 : Nat := 118140960795 + 6393256 * 2 ^ 59
def prefixEnd_6393256 : Nat := 4983230072969 + 3 ^ 40 * 6393256 * 2
def baseEnd_6393256 : Nat := 364757030582349287799773

theorem tailTrace_6393256 : CollatzResearch.WordTrace tailWord_6393256 prefixEnd_6393256 364757030582349287799773 := by
  unfold tailWord_6393256
  simp only [CollatzResearch.WordTrace]
  refine ⟨116590601463166434020403811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155454135284221912027205081 116590601463166434020403811)
  ·
    refine ⟨174885902194749651030605717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116590601463166434020403811 174885902194749651030605717)
    ·
      refine ⟨8197776665378889892059643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 174885902194749651030605717 8197776665378889892059643)
      ·
        refine ⟨12296664998068334838089465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8197776665378889892059643 12296664998068334838089465)
        ·
          refine ⟨9222498748551251128567099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12296664998068334838089465 9222498748551251128567099)
          ·
            refine ⟨13833748122826876692850649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9222498748551251128567099 13833748122826876692850649)
            ·
              refine ⟨10375311092120157519637987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13833748122826876692850649 10375311092120157519637987)
              ·
                refine ⟨15562966638180236279456981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10375311092120157519637987 15562966638180236279456981)
                ·
                  refine ⟨364757030582349287799773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15562966638180236279456981 364757030582349287799773)
                  ·
                    rfl

theorem cell23_6393256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 1, 7].length) (baseStart_6393256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6393256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6393256 prefixEnd_6393256 := by exact prefixLift 6393256
  have htrace : WordTrace (prefixWord ++ tailWord_6393256) baseStart_6393256 baseEnd_6393256 := by
    simpa [prefixWord, tailWord_6393256, baseEnd_6393256] using wordTrace_append hprefix tailTrace_6393256
  have hstable : (prefixWord ++ tailWord_6393256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6393256).length < 2 ^ (prefixWord ++ tailWord_6393256).sum := by decide
  have hdescent : baseEnd_6393256 < baseStart_6393256 := by decide
  rcases family_descends (prefixWord ++ tailWord_6393256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6393272 : List Nat := [2, 1, 2, 1, 2, 2, 3, 2, 1, 3, 4]
def baseStart_6393272 : Nat := 118140960795 + 6393272 * 2 ^ 59
def prefixEnd_6393272 : Nat := 4983230072969 + 3 ^ 40 * 6393272 * 2
def baseEnd_6393272 : Nat := 3282821490931615527597883

theorem tailTrace_6393272 : CollatzResearch.WordTrace tailWord_6393272 prefixEnd_6393272 3282821490931615527597883 := by
  unfold tailWord_6393272
  simp only [CollatzResearch.WordTrace]
  refine ⟨116590893247137451386695035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155454524329516601848926713 116590893247137451386695035)
  ·
    refine ⟨174886339870706177080042553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116590893247137451386695035 174886339870706177080042553)
    ·
      refine ⟨131164754903029632810031915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174886339870706177080042553 131164754903029632810031915)
      ·
        refine ⟨196747132354544449215047873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131164754903029632810031915 196747132354544449215047873)
        ·
          refine ⟨147560349265908336911285905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196747132354544449215047873 147560349265908336911285905)
          ·
            refine ⟨110670261949431252683464429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147560349265908336911285905 110670261949431252683464429)
            ·
              refine ⟨41501348231036719756299161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110670261949431252683464429 41501348231036719756299161)
              ·
                refine ⟨31126011173277539817224371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41501348231036719756299161 31126011173277539817224371)
                ·
                  refine ⟨46689016759916309725836557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31126011173277539817224371 46689016759916309725836557)
                  ·
                    refine ⟨17508381284968616147188709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46689016759916309725836557 17508381284968616147188709)
                    ·
                      refine ⟨3282821490931615527597883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17508381284968616147188709 3282821490931615527597883)
                      ·
                        rfl

theorem cell23_6393272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 1, 3, 4].length) (baseStart_6393272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6393272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6393272 prefixEnd_6393272 := by exact prefixLift 6393272
  have htrace : WordTrace (prefixWord ++ tailWord_6393272) baseStart_6393272 baseEnd_6393272 := by
    simpa [prefixWord, tailWord_6393272, baseEnd_6393272] using wordTrace_append hprefix tailTrace_6393272
  have hstable : (prefixWord ++ tailWord_6393272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6393272).length < 2 ^ (prefixWord ++ tailWord_6393272).sum := by decide
  have hdescent : baseEnd_6393272 < baseStart_6393272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6393272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6393316 : List Nat := [2, 3, 1, 1, 1, 1, 1, 8, 1, 4]
def baseStart_6393316 : Nat := 118140960795 + 6393316 * 2 ^ 59
def prefixEnd_6393316 : Nat := 4983230072969 + 3 ^ 40 * 6393316 * 2
def baseEnd_6393316 : Nat := 1094281361360137785149227

theorem tailTrace_6393316 : CollatzResearch.WordTrace tailWord_6393316 prefixEnd_6393316 1094281361360137785149227 := by
  unfold tailWord_6393316
  simp only [CollatzResearch.WordTrace]
  refine ⟨116591695653057749143995901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155455594204076998858661201 116591695653057749143995901)
  ·
    refine ⟨43721885869896655928998463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116591695653057749143995901 43721885869896655928998463)
    ·
      refine ⟨65582828804844983893497695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43721885869896655928998463 65582828804844983893497695)
      ·
        refine ⟨98374243207267475840246543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65582828804844983893497695 98374243207267475840246543)
        ·
          refine ⟨147561364810901213760369815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98374243207267475840246543 147561364810901213760369815)
          ·
            refine ⟨221342047216351820640554723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147561364810901213760369815 221342047216351820640554723)
            ·
              refine ⟨332013070824527730960832085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221342047216351820640554723 332013070824527730960832085)
              ·
                refine ⟨3890778173724934347197251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 332013070824527730960832085 3890778173724934347197251)
                ·
                  refine ⟨5836167260587401520795877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3890778173724934347197251 5836167260587401520795877)
                  ·
                    refine ⟨1094281361360137785149227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5836167260587401520795877 1094281361360137785149227)
                    ·
                      rfl

theorem cell23_6393316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 8, 1, 4].length) (baseStart_6393316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6393316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6393316 prefixEnd_6393316 := by exact prefixLift 6393316
  have htrace : WordTrace (prefixWord ++ tailWord_6393316) baseStart_6393316 baseEnd_6393316 := by
    simpa [prefixWord, tailWord_6393316, baseEnd_6393316] using wordTrace_append hprefix tailTrace_6393316
  have hstable : (prefixWord ++ tailWord_6393316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6393316).length < 2 ^ (prefixWord ++ tailWord_6393316).sum := by decide
  have hdescent : baseEnd_6393316 < baseStart_6393316 := by decide
  rcases family_descends (prefixWord ++ tailWord_6393316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6393329 : List Nat := [1, 2, 2, 2, 3, 3, 1, 3, 6]
def baseStart_6393329 : Nat := 118140960795 + 6393329 * 2 ^ 59
def prefixEnd_6393329 : Nat := 4983230072969 + 3 ^ 40 * 6393329 * 2
def baseEnd_6393329 : Nat := 364761195480991311620569

theorem tailTrace_6393329 : CollatzResearch.WordTrace tailWord_6393329 prefixEnd_6393329 364761195480991311620569 := by
  unfold tailWord_6393329
  simp only [CollatzResearch.WordTrace]
  refine ⟨233183865455068401508215041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155455910303378934338810027 233183865455068401508215041)
  ·
    refine ⟨174887899091301301131161281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233183865455068401508215041 174887899091301301131161281)
    ·
      refine ⟨131165924318475975848370961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174887899091301301131161281 131165924318475975848370961)
      ·
        refine ⟨98374443238856981886278221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131165924318475975848370961 98374443238856981886278221)
        ·
          refine ⟨36890416214571368207354333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98374443238856981886278221 36890416214571368207354333)
          ·
            refine ⟨13833906080464263077757875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36890416214571368207354333 13833906080464263077757875)
            ·
              refine ⟨20750859120696394616636813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13833906080464263077757875 20750859120696394616636813)
              ·
                refine ⟨7781572170261147981238805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20750859120696394616636813 7781572170261147981238805)
                ·
                  refine ⟨364761195480991311620569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7781572170261147981238805 364761195480991311620569)
                  ·
                    rfl

theorem cell23_6393329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 3, 6].length) (baseStart_6393329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6393329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6393329 prefixEnd_6393329 := by exact prefixLift 6393329
  have htrace : WordTrace (prefixWord ++ tailWord_6393329) baseStart_6393329 baseEnd_6393329 := by
    simpa [prefixWord, tailWord_6393329, baseEnd_6393329] using wordTrace_append hprefix tailTrace_6393329
  have hstable : (prefixWord ++ tailWord_6393329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6393329).length < 2 ^ (prefixWord ++ tailWord_6393329).sum := by decide
  have hdescent : baseEnd_6393329 < baseStart_6393329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6393329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6393453 : List Nat := [1, 5, 1, 1, 4, 2, 2, 7]
def baseStart_6393453 : Nat := 118140960795 + 6393453 * 2 ^ 59
def prefixEnd_6393453 : Nat := 4983230072969 + 3 ^ 40 * 6393453 * 2
def baseEnd_6393453 : Nat := 121589423367780715534613

theorem tailTrace_6393453 : CollatzResearch.WordTrace tailWord_6393453 prefixEnd_6393453 121589423367780715534613 := by
  unfold tailWord_6393453
  simp only [CollatzResearch.WordTrace]
  refine ⟨233188388106619170685729013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155458925404412780457152675 233188388106619170685729013)
  ·
    refine ⟨21861411384995547251787095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 233188388106619170685729013 21861411384995547251787095)
    ·
      refine ⟨32792117077493320877680643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21861411384995547251787095 32792117077493320877680643)
      ·
        refine ⟨49188175616239981316520965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32792117077493320877680643 49188175616239981316520965)
        ·
          refine ⟨9222782928044996496847681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49188175616239981316520965 9222782928044996496847681)
          ·
            refine ⟨6917087196033747372635761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9222782928044996496847681 6917087196033747372635761)
            ·
              refine ⟨5187815397025310529476821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6917087196033747372635761 5187815397025310529476821)
              ·
                refine ⟨121589423367780715534613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5187815397025310529476821 121589423367780715534613)
                ·
                  rfl

theorem cell23_6393453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2, 7].length) (baseStart_6393453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6393453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6393453 prefixEnd_6393453 := by exact prefixLift 6393453
  have htrace : WordTrace (prefixWord ++ tailWord_6393453) baseStart_6393453 baseEnd_6393453 := by
    simpa [prefixWord, tailWord_6393453, baseEnd_6393453] using wordTrace_append hprefix tailTrace_6393453
  have hstable : (prefixWord ++ tailWord_6393453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6393453).length < 2 ^ (prefixWord ++ tailWord_6393453).sum := by decide
  have hdescent : baseEnd_6393453 < baseStart_6393453 := by decide
  rcases family_descends (prefixWord ++ tailWord_6393453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6393509 : List Nat := [1, 3, 1, 2, 1, 2, 2, 4, 7]
def baseStart_6393509 : Nat := 118140960795 + 6393509 * 2 ^ 59
def prefixEnd_6393509 : Nat := 4983230072969 + 3 ^ 40 * 6393509 * 2
def baseEnd_6393509 : Nat := 364771465094081233370477

theorem tailTrace_6393509 : CollatzResearch.WordTrace tailWord_6393509 prefixEnd_6393509 364771465094081233370477 := by
  unfold tailWord_6393509
  simp only [CollatzResearch.WordTrace]
  refine ⟨233190430594416292249767581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155460287062944194833178387 233190430594416292249767581)
  ·
    refine ⟨87446411472906109593662843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233190430594416292249767581 87446411472906109593662843)
    ·
      refine ⟨131169617209359164390494265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87446411472906109593662843 131169617209359164390494265)
      ·
        refine ⟨98377212907019373292870699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131169617209359164390494265 98377212907019373292870699)
        ·
          refine ⟨147565819360529059939306049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98377212907019373292870699 147565819360529059939306049)
          ·
            refine ⟨110674364520396794954479537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147565819360529059939306049 110674364520396794954479537)
            ·
              refine ⟨83005773390297596215859653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110674364520396794954479537 83005773390297596215859653)
              ·
                refine ⟨15563582510680799290473685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83005773390297596215859653 15563582510680799290473685)
                ·
                  refine ⟨364771465094081233370477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15563582510680799290473685 364771465094081233370477)
                  ·
                    rfl

theorem cell23_6393509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4, 7].length) (baseStart_6393509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6393509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6393509 prefixEnd_6393509 := by exact prefixLift 6393509
  have htrace : WordTrace (prefixWord ++ tailWord_6393509) baseStart_6393509 baseEnd_6393509 := by
    simpa [prefixWord, tailWord_6393509, baseEnd_6393509] using wordTrace_append hprefix tailTrace_6393509
  have hstable : (prefixWord ++ tailWord_6393509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6393509).length < 2 ^ (prefixWord ++ tailWord_6393509).sum := by decide
  have hdescent : baseEnd_6393509 < baseStart_6393509 := by decide
  rcases family_descends (prefixWord ++ tailWord_6393509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6393536 : List Nat := [2, 1, 1, 2, 4, 1, 2, 2, 2, 3, 3]
def baseStart_6393536 : Nat := 118140960795 + 6393536 * 2 ^ 59
def prefixEnd_6393536 : Nat := 4983230072969 + 3 ^ 40 * 6393536 * 2
def baseEnd_6393536 : Nat := 3282957049824402494696669

theorem tailTrace_6393536 : CollatzResearch.WordTrace tailWord_6393536 prefixEnd_6393536 3282957049824402494696669 := by
  unfold tailWord_6393536
  simp only [CollatzResearch.WordTrace]
  refine ⟨116595707682659237930500231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155460943576878983907333641 116595707682659237930500231)
  ·
    refine ⟨174893561523988856895750347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116595707682659237930500231 174893561523988856895750347)
    ·
      refine ⟨262340342285983285343625521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174893561523988856895750347 262340342285983285343625521)
      ·
        refine ⟨196755256714487464007719141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262340342285983285343625521 196755256714487464007719141)
        ·
          refine ⟨36891610633966399501447339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 196755256714487464007719141 36891610633966399501447339)
          ·
            refine ⟨55337415950949599252171009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36891610633966399501447339 55337415950949599252171009)
            ·
              refine ⟨41503061963212199439128257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55337415950949599252171009 41503061963212199439128257)
              ·
                refine ⟨31127296472409149579346193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41503061963212199439128257 31127296472409149579346193)
                ·
                  refine ⟨23345472354306862184509645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31127296472409149579346193 23345472354306862184509645)
                  ·
                    refine ⟨8754552132865073319191117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23345472354306862184509645 8754552132865073319191117)
                    ·
                      refine ⟨3282957049824402494696669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8754552132865073319191117 3282957049824402494696669)
                      ·
                        rfl

theorem cell23_6393536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3, 3].length) (baseStart_6393536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6393536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6393536 prefixEnd_6393536 := by exact prefixLift 6393536
  have htrace : WordTrace (prefixWord ++ tailWord_6393536) baseStart_6393536 baseEnd_6393536 := by
    simpa [prefixWord, tailWord_6393536, baseEnd_6393536] using wordTrace_append hprefix tailTrace_6393536
  have hstable : (prefixWord ++ tailWord_6393536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6393536).length < 2 ^ (prefixWord ++ tailWord_6393536).sum := by decide
  have hdescent : baseEnd_6393536 < baseStart_6393536 := by decide
  rcases family_descends (prefixWord ++ tailWord_6393536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6393637 : List Nat := [1, 3, 1, 2, 3, 4, 1, 3, 1, 4]
def baseStart_6393637 : Nat := 118140960795 + 6393637 * 2 ^ 59
def prefixEnd_6393637 : Nat := 4983230072969 + 3 ^ 40 * 6393637 * 2
def baseEnd_6393637 : Nat := 1094336303790168866511235

theorem tailTrace_6393637 : CollatzResearch.WordTrace tailWord_6393637 prefixEnd_6393637 1094336303790168866511235 := by
  unfold tailWord_6393637
  simp only [CollatzResearch.WordTrace]
  refine ⟨233195099137952570110427165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155463399425301713406951443 233195099137952570110427165)
  ·
    refine ⟨87448162176732213791410187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233195099137952570110427165 87448162176732213791410187)
    ·
      refine ⟨131172243265098320687115281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87448162176732213791410187 131172243265098320687115281)
      ·
        refine ⟨98379182448823740515336461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131172243265098320687115281 98379182448823740515336461)
        ·
          refine ⟨36892193418308902693251173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98379182448823740515336461 36892193418308902693251173)
          ·
            refine ⟨6917286265932919254984595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36892193418308902693251173 6917286265932919254984595)
            ·
              refine ⟨10375929398899378882476893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6917286265932919254984595 10375929398899378882476893)
              ·
                refine ⟨3890973524587267080928835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10375929398899378882476893 3890973524587267080928835)
                ·
                  refine ⟨5836460286880900621393253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3890973524587267080928835 5836460286880900621393253)
                  ·
                    refine ⟨1094336303790168866511235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5836460286880900621393253 1094336303790168866511235)
                    ·
                      rfl

theorem cell23_6393637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 3, 1, 4].length) (baseStart_6393637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6393637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6393637 prefixEnd_6393637 := by exact prefixLift 6393637
  have htrace : WordTrace (prefixWord ++ tailWord_6393637) baseStart_6393637 baseEnd_6393637 := by
    simpa [prefixWord, tailWord_6393637, baseEnd_6393637] using wordTrace_append hprefix tailTrace_6393637
  have hstable : (prefixWord ++ tailWord_6393637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6393637).length < 2 ^ (prefixWord ++ tailWord_6393637).sum := by decide
  have hdescent : baseEnd_6393637 < baseStart_6393637 := by decide
  rcases family_descends (prefixWord ++ tailWord_6393637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6393660 : List Nat := [2, 2, 2, 2, 1, 1, 5, 1, 3, 1, 3]
def baseStart_6393660 : Nat := 118140960795 + 6393660 * 2 ^ 59
def prefixEnd_6393660 : Nat := 4983230072969 + 3 ^ 40 * 6393660 * 2
def baseEnd_6393660 : Nat := 3283020721425560009546099

theorem tailTrace_6393660 : CollatzResearch.WordTrace tailWord_6393660 prefixEnd_6393660 3283020721425560009546099 := by
  unfold tailWord_6393660
  simp only [CollatzResearch.WordTrace]
  refine ⟨116597969008434622519257217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155463958677912830025676289 116597969008434622519257217)
  ·
    refine ⟨87448476756325966889442913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116597969008434622519257217 87448476756325966889442913)
    ·
      refine ⟨65586357567244475167082185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87448476756325966889442913 65586357567244475167082185)
      ·
        refine ⟨49189768175433356375311639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65586357567244475167082185 49189768175433356375311639)
        ·
          refine ⟨73784652263150034562967459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49189768175433356375311639 73784652263150034562967459)
          ·
            refine ⟨110676978394725051844451189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73784652263150034562967459 110676978394725051844451189)
            ·
              refine ⟨10375966724505473610417299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 110676978394725051844451189 10375966724505473610417299)
              ·
                refine ⟨15563950086758210415625949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10375966724505473610417299 15563950086758210415625949)
                ·
                  refine ⟨5836481282534328905859731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15563950086758210415625949 5836481282534328905859731)
                  ·
                    refine ⟨8754721923801493358789597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5836481282534328905859731 8754721923801493358789597)
                    ·
                      refine ⟨3283020721425560009546099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8754721923801493358789597 3283020721425560009546099)
                      ·
                        rfl

theorem cell23_6393660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 1, 3, 1, 3].length) (baseStart_6393660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6393660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6393660 prefixEnd_6393660 := by exact prefixLift 6393660
  have htrace : WordTrace (prefixWord ++ tailWord_6393660) baseStart_6393660 baseEnd_6393660 := by
    simpa [prefixWord, tailWord_6393660, baseEnd_6393660] using wordTrace_append hprefix tailTrace_6393660
  have hstable : (prefixWord ++ tailWord_6393660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6393660).length < 2 ^ (prefixWord ++ tailWord_6393660).sum := by decide
  have hdescent : baseEnd_6393660 < baseStart_6393660 := by decide
  rcases family_descends (prefixWord ++ tailWord_6393660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6393687 : List Nat := [1, 1, 3, 2, 5, 1, 2, 1, 2, 3, 2]
def baseStart_6393687 : Nat := 118140960795 + 6393687 * 2 ^ 59
def prefixEnd_6393687 : Nat := 4983230072969 + 3 ^ 40 * 6393687 * 2
def baseEnd_6393687 : Nat := 3283034585403231403908475

theorem tailTrace_6393687 : CollatzResearch.WordTrace tailWord_6393687 prefixEnd_6393687 3283034585403231403908475 := by
  unfold tailWord_6393687
  simp only [CollatzResearch.WordTrace]
  refine ⟨233196922787771428649747315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155464615191847619099831543 233196922787771428649747315)
  ·
    refine ⟨349795384181657142974620973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233196922787771428649747315 349795384181657142974620973)
    ·
      refine ⟨131173269068121428615482865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 349795384181657142974620973 131173269068121428615482865)
      ·
        refine ⟨98379951801091071461612149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131173269068121428615482865 98379951801091071461612149)
        ·
          refine ⟨9223120481352287949526139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 98379951801091071461612149 9223120481352287949526139)
          ·
            refine ⟨13834680722028431924289209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9223120481352287949526139 13834680722028431924289209)
            ·
              refine ⟨10376010541521323943216907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13834680722028431924289209 10376010541521323943216907)
              ·
                refine ⟨15564015812281985914825361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10376010541521323943216907 15564015812281985914825361)
                ·
                  refine ⟨11673011859211489436119021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15564015812281985914825361 11673011859211489436119021)
                  ·
                    refine ⟨4377379447204308538544633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11673011859211489436119021 4377379447204308538544633)
                    ·
                      refine ⟨3283034585403231403908475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4377379447204308538544633 3283034585403231403908475)
                      ·
                        rfl

theorem cell23_6393687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 1, 2, 3, 2].length) (baseStart_6393687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6393687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6393687 prefixEnd_6393687 := by exact prefixLift 6393687
  have htrace : WordTrace (prefixWord ++ tailWord_6393687) baseStart_6393687 baseEnd_6393687 := by
    simpa [prefixWord, tailWord_6393687, baseEnd_6393687] using wordTrace_append hprefix tailTrace_6393687
  have hstable : (prefixWord ++ tailWord_6393687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6393687).length < 2 ^ (prefixWord ++ tailWord_6393687).sum := by decide
  have hdescent : baseEnd_6393687 < baseStart_6393687 := by decide
  rcases family_descends (prefixWord ++ tailWord_6393687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6393717 : List Nat := [1, 3, 4, 1, 1, 1, 2, 3, 3, 2, 2]
def baseStart_6393717 : Nat := 118140960795 + 6393717 * 2 ^ 59
def prefixEnd_6393717 : Nat := 4983230072969 + 3 ^ 40 * 6393717 * 2
def baseEnd_6393717 : Nat := 3283049989822866286533337

theorem tailTrace_6393717 : CollatzResearch.WordTrace tailWord_6393717 prefixEnd_6393717 3283049989822866286533337 := by
  unfold tailWord_6393717
  simp only [CollatzResearch.WordTrace]
  refine ⟨233198016977662743773339405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155465344651775162515559603 233198016977662743773339405)
  ·
    refine ⟨87449256366623528915002277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233198016977662743773339405 87449256366623528915002277)
    ·
      refine ⟨16396735568741911671562927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87449256366623528915002277 16396735568741911671562927)
      ·
        refine ⟨24595103353112867507344391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16396735568741911671562927 24595103353112867507344391)
        ·
          refine ⟨36892655029669301261016587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24595103353112867507344391 36892655029669301261016587)
          ·
            refine ⟨55338982544503951891524881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36892655029669301261016587 55338982544503951891524881)
            ·
              refine ⟨41504236908377963918643661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55338982544503951891524881 41504236908377963918643661)
              ·
                refine ⟨15564088840641736469491373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41504236908377963918643661 15564088840641736469491373)
                ·
                  refine ⟨5836533315240651176059265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15564088840641736469491373 5836533315240651176059265)
                  ·
                    refine ⟨4377399986430488382044449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5836533315240651176059265 4377399986430488382044449)
                    ·
                      refine ⟨3283049989822866286533337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4377399986430488382044449 3283049989822866286533337)
                      ·
                        rfl

theorem cell23_6393717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_6393717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6393717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6393717 prefixEnd_6393717 := by exact prefixLift 6393717
  have htrace : WordTrace (prefixWord ++ tailWord_6393717) baseStart_6393717 baseEnd_6393717 := by
    simpa [prefixWord, tailWord_6393717, baseEnd_6393717] using wordTrace_append hprefix tailTrace_6393717
  have hstable : (prefixWord ++ tailWord_6393717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6393717).length < 2 ^ (prefixWord ++ tailWord_6393717).sum := by decide
  have hdescent : baseEnd_6393717 < baseStart_6393717 := by decide
  rcases family_descends (prefixWord ++ tailWord_6393717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6393754 : List Nat := [3, 1, 1, 4, 2, 3, 2, 1, 1, 2, 3]
def baseStart_6393754 : Nat := 118140960795 + 6393754 * 2 ^ 59
def prefixEnd_6393754 : Nat := 4983230072969 + 3 ^ 40 * 6393754 * 2
def baseEnd_6393754 : Nat := 3283068988607082641770667

theorem tailTrace_6393754 : CollatzResearch.WordTrace tailWord_6393754 prefixEnd_6393754 3283068988607082641770667 := by
  unfold tailWord_6393754
  simp only [CollatzResearch.WordTrace]
  refine ⟨58299841619632174773109079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155466244319019132728290877 58299841619632174773109079)
  ·
    refine ⟨87449762429448262159663619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58299841619632174773109079 87449762429448262159663619)
    ·
      refine ⟨131174643644172393239495429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87449762429448262159663619 131174643644172393239495429)
      ·
        refine ⟨24595245683282323732405393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131174643644172393239495429 24595245683282323732405393)
        ·
          refine ⟨18446434262461742799304045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24595245683282323732405393 18446434262461742799304045)
          ·
            refine ⟨6917412848423153549739017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18446434262461742799304045 6917412848423153549739017)
            ·
              refine ⟨5188059636317365162304263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6917412848423153549739017 5188059636317365162304263)
              ·
                refine ⟨7782089454476047743456395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5188059636317365162304263 7782089454476047743456395)
                ·
                  refine ⟨11673134181714071615184593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7782089454476047743456395 11673134181714071615184593)
                  ·
                    refine ⟨8754850636285553711388445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11673134181714071615184593 8754850636285553711388445)
                    ·
                      refine ⟨3283068988607082641770667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8754850636285553711388445 3283068988607082641770667)
                      ·
                        rfl

theorem cell23_6393754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_6393754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6393754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6393754 prefixEnd_6393754 := by exact prefixLift 6393754
  have htrace : WordTrace (prefixWord ++ tailWord_6393754) baseStart_6393754 baseEnd_6393754 := by
    simpa [prefixWord, tailWord_6393754, baseEnd_6393754] using wordTrace_append hprefix tailTrace_6393754
  have hstable : (prefixWord ++ tailWord_6393754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6393754).length < 2 ^ (prefixWord ++ tailWord_6393754).sum := by decide
  have hdescent : baseEnd_6393754 < baseStart_6393754 := by decide
  rcases family_descends (prefixWord ++ tailWord_6393754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6393767 : List Nat := [1, 1, 6, 1, 2, 2, 1, 1, 4, 1, 3]
def baseStart_6393767 : Nat := 118140960795 + 6393767 * 2 ^ 59
def prefixEnd_6393767 : Nat := 4983230072969 + 3 ^ 40 * 6393767 * 2
def baseEnd_6393767 : Nat := 3283075663855591090908107

theorem tailTrace_6393767 : CollatzResearch.WordTrace tailWord_6393767 prefixEnd_6393767 3283075663855591090908107 := by
  unfold tailWord_6393767
  simp only [CollatzResearch.WordTrace]
  refine ⟨233199840627481602312659555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155466560418321068208439703 233199840627481602312659555)
  ·
    refine ⟨349799760941222403468989333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233199840627481602312659555 349799760941222403468989333)
    ·
      refine ⟨16396863794119800162608875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 349799760941222403468989333 16396863794119800162608875)
      ·
        refine ⟨24595295691179700243913313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16396863794119800162608875 24595295691179700243913313)
        ·
          refine ⟨18446471768384775182934985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24595295691179700243913313 18446471768384775182934985)
          ·
            refine ⟨13834853826288581387201239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18446471768384775182934985 13834853826288581387201239)
            ·
              refine ⟨20752280739432872080801859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13834853826288581387201239 20752280739432872080801859)
              ·
                refine ⟨31128421109149308121202789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20752280739432872080801859 31128421109149308121202789)
                ·
                  refine ⟨5836578957965495272725523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31128421109149308121202789 5836578957965495272725523)
                  ·
                    refine ⟨8754868436948242909088285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5836578957965495272725523 8754868436948242909088285)
                    ·
                      refine ⟨3283075663855591090908107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8754868436948242909088285 3283075663855591090908107)
                      ·
                        rfl

theorem cell23_6393767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_6393767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6393767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6393767 prefixEnd_6393767 := by exact prefixLift 6393767
  have htrace : WordTrace (prefixWord ++ tailWord_6393767) baseStart_6393767 baseEnd_6393767 := by
    simpa [prefixWord, tailWord_6393767, baseEnd_6393767] using wordTrace_append hprefix tailTrace_6393767
  have hstable : (prefixWord ++ tailWord_6393767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6393767).length < 2 ^ (prefixWord ++ tailWord_6393767).sum := by decide
  have hdescent : baseEnd_6393767 < baseStart_6393767 := by decide
  rcases family_descends (prefixWord ++ tailWord_6393767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6393862 : List Nat := [6, 2, 1, 2, 1, 1, 3, 1, 1, 3, 2]
def baseStart_6393862 : Nat := 118140960795 + 6393862 * 2 ^ 59
def prefixEnd_6393862 : Nat := 4983230072969 + 3 ^ 40 * 6393862 * 2
def baseEnd_6393862 : Nat := 3283124444517768219220171

theorem tailTrace_6393862 : CollatzResearch.WordTrace tailWord_6393862 prefixEnd_6393862 3283124444517768219220171 := by
  unfold tailWord_6393862
  simp only [CollatzResearch.WordTrace]
  refine ⟨7287603298816794798042745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 155468870374758289024911893 7287603298816794798042745)
  ·
    refine ⟨5465702474112596098532059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7287603298816794798042745 5465702474112596098532059)
    ·
      refine ⟨8198553711168894147798089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5465702474112596098532059 8198553711168894147798089)
      ·
        refine ⟨6148915283376670610848567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8198553711168894147798089 6148915283376670610848567)
        ·
          refine ⟨9223372925065005916272851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6148915283376670610848567 9223372925065005916272851)
          ·
            refine ⟨13835059387597508874409277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9223372925065005916272851 13835059387597508874409277)
            ·
              refine ⟨5188147270349065827903479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13835059387597508874409277 5188147270349065827903479)
              ·
                refine ⟨7782220905523598741855219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5188147270349065827903479 7782220905523598741855219)
                ·
                  refine ⟨11673331358285398112782829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7782220905523598741855219 11673331358285398112782829)
                  ·
                    refine ⟨4377499259357024292293561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11673331358285398112782829 4377499259357024292293561)
                    ·
                      refine ⟨3283124444517768219220171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4377499259357024292293561 3283124444517768219220171)
                      ·
                        rfl

theorem cell23_6393862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_6393862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6393862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6393862 prefixEnd_6393862 := by exact prefixLift 6393862
  have htrace : WordTrace (prefixWord ++ tailWord_6393862) baseStart_6393862 baseEnd_6393862 := by
    simpa [prefixWord, tailWord_6393862, baseEnd_6393862] using wordTrace_append hprefix tailTrace_6393862
  have hstable : (prefixWord ++ tailWord_6393862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6393862).length < 2 ^ (prefixWord ++ tailWord_6393862).sum := by decide
  have hdescent : baseEnd_6393862 < baseStart_6393862 := by decide
  rcases family_descends (prefixWord ++ tailWord_6393862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6393880 : List Nat := [2, 1, 2, 3, 2, 1, 1, 4, 2, 1, 4]
def baseStart_6393880 : Nat := 118140960795 + 6393880 * 2 ^ 59
def prefixEnd_6393880 : Nat := 4983230072969 + 3 ^ 40 * 6393880 * 2
def baseEnd_6393880 : Nat := 3283133687169549148795087

theorem tailTrace_6393880 : CollatzResearch.WordTrace tailWord_6393880 prefixEnd_6393880 3283133687169549148795087 := by
  unfold tailWord_6393880
  simp only [CollatzResearch.WordTrace]
  refine ⟨116601981038036111305761547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155469308050714815074348729 116601981038036111305761547)
  ·
    refine ⟨174902971557054166958642321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116601981038036111305761547 174902971557054166958642321)
    ·
      refine ⟨131177228667790625218981741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174902971557054166958642321 131177228667790625218981741)
      ·
        refine ⟨49191460750421484457118153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131177228667790625218981741 49191460750421484457118153)
        ·
          refine ⟨36893595562816113342838615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49191460750421484457118153 36893595562816113342838615)
          ·
            refine ⟨55340393344224170014257923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36893595562816113342838615 55340393344224170014257923)
            ·
              refine ⟨83010590016336255021386885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55340393344224170014257923 83010590016336255021386885)
              ·
                refine ⟨15564485628063047816510041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83010590016336255021386885 15564485628063047816510041)
                ·
                  refine ⟨11673364221047285862382531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15564485628063047816510041 11673364221047285862382531)
                  ·
                    refine ⟨17510046331570928793573797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11673364221047285862382531 17510046331570928793573797)
                    ·
                      refine ⟨3283133687169549148795087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17510046331570928793573797 3283133687169549148795087)
                      ·
                        rfl

theorem cell23_6393880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_6393880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6393880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6393880 prefixEnd_6393880 := by exact prefixLift 6393880
  have htrace : WordTrace (prefixWord ++ tailWord_6393880) baseStart_6393880 baseEnd_6393880 := by
    simpa [prefixWord, tailWord_6393880, baseEnd_6393880] using wordTrace_append hprefix tailTrace_6393880
  have hstable : (prefixWord ++ tailWord_6393880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6393880).length < 2 ^ (prefixWord ++ tailWord_6393880).sum := by decide
  have hdescent : baseEnd_6393880 < baseStart_6393880 := by decide
  rcases family_descends (prefixWord ++ tailWord_6393880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6393957 : List Nat := [1, 3, 1, 3, 2, 2, 1, 2, 1, 5, 2]
def baseStart_6393957 : Nat := 118140960795 + 6393957 * 2 ^ 59
def prefixEnd_6393957 : Nat := 4983230072969 + 3 ^ 40 * 6393957 * 2
def baseEnd_6393957 : Nat := 3283173225179945347532233

theorem tailTrace_6393957 : CollatzResearch.WordTrace tailWord_6393957 prefixEnd_6393957 3283173225179945347532233 := by
  unfold tailWord_6393957
  simp only [CollatzResearch.WordTrace]
  refine ⟨233206770496793264762076125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155471180331195509841384083 233206770496793264762076125)
  ·
    refine ⟨87452538936297474285778547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233206770496793264762076125 87452538936297474285778547)
    ·
      refine ⟨131178808404446211428667821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87452538936297474285778547 131178808404446211428667821)
      ·
        refine ⟨49192053151667329285750433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131178808404446211428667821 49192053151667329285750433)
        ·
          refine ⟨36894039863750496964312825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49192053151667329285750433 36894039863750496964312825)
          ·
            refine ⟨27670529897812872723234619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36894039863750496964312825 27670529897812872723234619)
            ·
              refine ⟨41505794846719309084851929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27670529897812872723234619 41505794846719309084851929)
              ·
                refine ⟨31129346135039481813638947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41505794846719309084851929 31129346135039481813638947)
                ·
                  refine ⟨46694019202559222720458421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31129346135039481813638947 46694019202559222720458421)
                  ·
                    refine ⟨4377564300239927130042977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46694019202559222720458421 4377564300239927130042977)
                    ·
                      refine ⟨3283173225179945347532233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4377564300239927130042977 3283173225179945347532233)
                      ·
                        rfl

theorem cell23_6393957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 5, 2].length) (baseStart_6393957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6393957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6393957 prefixEnd_6393957 := by exact prefixLift 6393957
  have htrace : WordTrace (prefixWord ++ tailWord_6393957) baseStart_6393957 baseEnd_6393957 := by
    simpa [prefixWord, tailWord_6393957, baseEnd_6393957] using wordTrace_append hprefix tailTrace_6393957
  have hstable : (prefixWord ++ tailWord_6393957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6393957).length < 2 ^ (prefixWord ++ tailWord_6393957).sum := by decide
  have hdescent : baseEnd_6393957 < baseStart_6393957 := by decide
  rcases family_descends (prefixWord ++ tailWord_6393957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
