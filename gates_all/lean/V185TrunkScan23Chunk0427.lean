import V185TrunkScan23Chunk0426

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2523883 : List Nat := [1, 1, 1, 1, 2, 4, 1, 2, 2, 3, 5]
def baseStart_2523883 : Nat := 118140960795 + 2523883 * 2 ^ 59
def prefixEnd_2523883 : Nat := 4983230072969 + 3 ^ 40 * 2523883 * 2
def baseEnd_2523883 : Nat := 1295965094711654029855379

theorem tailTrace_2523883 : CollatzResearch.WordTrace tailWord_2523883 prefixEnd_2523883 1295965094711654029855379 := by
  unfold tailWord_2523883
  simp only [CollatzResearch.WordTrace]
  refine ⟨92053575515410410744272303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61369050343606940496181535 92053575515410410744272303)
  ·
    refine ⟨138080363273115616116408455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92053575515410410744272303 138080363273115616116408455)
    ·
      refine ⟨207120544909673424174612683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138080363273115616116408455 207120544909673424174612683)
      ·
        refine ⟨310680817364510136261919025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207120544909673424174612683 310680817364510136261919025)
        ·
          refine ⟨233010613023382602196439269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 310680817364510136261919025 233010613023382602196439269)
          ·
            refine ⟨43689489941884237911832363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 233010613023382602196439269 43689489941884237911832363)
            ·
              refine ⟨65534234912826356867748545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43689489941884237911832363 65534234912826356867748545)
              ·
                refine ⟨49150676184619767650811409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65534234912826356867748545 49150676184619767650811409)
                ·
                  refine ⟨36863007138464825738108557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49150676184619767650811409 36863007138464825738108557)
                  ·
                    refine ⟨13823627676924309651790709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36863007138464825738108557 13823627676924309651790709)
                    ·
                      refine ⟨1295965094711654029855379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13823627676924309651790709 1295965094711654029855379)
                      ·
                        rfl

theorem cell23_2523883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3, 5].length) (baseStart_2523883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2523883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2523883 prefixEnd_2523883 := by exact prefixLift 2523883
  have htrace : WordTrace (prefixWord ++ tailWord_2523883) baseStart_2523883 baseEnd_2523883 := by
    simpa [prefixWord, tailWord_2523883, baseEnd_2523883] using wordTrace_append hprefix tailTrace_2523883
  have hstable : (prefixWord ++ tailWord_2523883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523883).length < 2 ^ (prefixWord ++ tailWord_2523883).sum := by decide
  have hdescent : baseEnd_2523883 < baseStart_2523883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523958 : List Nat := [5, 1, 2, 2, 2, 1, 1, 4, 1, 4]
def baseStart_2523958 : Nat := 118140960795 + 2523958 * 2 ^ 59
def prefixEnd_2523958 : Nat := 4983230072969 + 3 ^ 40 * 2523958 * 2
def baseEnd_2523958 : Nat := 432001201920247078805845

theorem tailTrace_2523958 : CollatzResearch.WordTrace tailWord_2523958 prefixEnd_2523958 432001201920247078805845 := by
  unfold tailWord_2523958
  simp only [CollatzResearch.WordTrace]
  refine ⟨5753519436883668659578283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61370873993425799035501685 5753519436883668659578283)
  ·
    refine ⟨8630279155325502989367425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5753519436883668659578283 8630279155325502989367425)
    ·
      refine ⟨6472709366494127242025569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8630279155325502989367425 6472709366494127242025569)
      ·
        refine ⟨4854532024870595431519177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6472709366494127242025569 4854532024870595431519177)
        ·
          refine ⟨3640899018652946573639383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4854532024870595431519177 3640899018652946573639383)
          ·
            refine ⟨5461348527979419860459075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3640899018652946573639383 5461348527979419860459075)
            ·
              refine ⟨8192022791969129790688613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5461348527979419860459075 8192022791969129790688613)
              ·
                refine ⟨1536004273494211835754115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8192022791969129790688613 1536004273494211835754115)
                ·
                  refine ⟨2304006410241317753631173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1536004273494211835754115 2304006410241317753631173)
                  ·
                    refine ⟨432001201920247078805845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2304006410241317753631173 432001201920247078805845)
                    ·
                      rfl

theorem cell23_2523958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_2523958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2523958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2523958 prefixEnd_2523958 := by exact prefixLift 2523958
  have htrace : WordTrace (prefixWord ++ tailWord_2523958) baseStart_2523958 baseEnd_2523958 := by
    simpa [prefixWord, tailWord_2523958, baseEnd_2523958] using wordTrace_append hprefix tailTrace_2523958
  have hstable : (prefixWord ++ tailWord_2523958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523958).length < 2 ^ (prefixWord ++ tailWord_2523958).sum := by decide
  have hdescent : baseEnd_2523958 < baseStart_2523958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2523991 : List Nat := [1, 1, 3, 2, 4, 3, 1, 1, 2, 3, 2]
def baseStart_2523991 : Nat := 118140960795 + 2523991 * 2 ^ 59
def prefixEnd_2523991 : Nat := 4983230072969 + 3 ^ 40 * 2523991 * 2
def baseEnd_2523991 : Nat := 1296020550622339607304883

theorem tailTrace_2523991 : CollatzResearch.WordTrace tailWord_2523991 prefixEnd_2523991 1296020550622339607304883 := by
  unfold tailWord_2523991
  simp only [CollatzResearch.WordTrace]
  refine ⟨92057514599019145189203827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61371676399346096792802551 92057514599019145189203827)
  ·
    refine ⟨138086271898528717783805741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92057514599019145189203827 138086271898528717783805741)
    ·
      refine ⟨51782351961948269168927153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138086271898528717783805741 51782351961948269168927153)
      ·
        refine ⟨38836763971461201876695365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51782351961948269168927153 38836763971461201876695365)
        ·
          refine ⟨7281893244648975351880381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38836763971461201876695365 7281893244648975351880381)
          ·
            refine ⟨2730709966743365756955143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7281893244648975351880381 2730709966743365756955143)
            ·
              refine ⟨4096064950115048635432715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2730709966743365756955143 4096064950115048635432715)
              ·
                refine ⟨6144097425172572953149073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4096064950115048635432715 6144097425172572953149073)
                ·
                  refine ⟨4608073068879429714861805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6144097425172572953149073 4608073068879429714861805)
                  ·
                    refine ⟨1728027400829786143073177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4608073068879429714861805 1728027400829786143073177)
                    ·
                      refine ⟨1296020550622339607304883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1728027400829786143073177 1296020550622339607304883)
                      ·
                        rfl

theorem cell23_2523991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 1, 2, 3, 2].length) (baseStart_2523991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2523991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2523991 prefixEnd_2523991 := by exact prefixLift 2523991
  have htrace : WordTrace (prefixWord ++ tailWord_2523991) baseStart_2523991 baseEnd_2523991 := by
    simpa [prefixWord, tailWord_2523991, baseEnd_2523991] using wordTrace_append hprefix tailTrace_2523991
  have hstable : (prefixWord ++ tailWord_2523991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2523991).length < 2 ^ (prefixWord ++ tailWord_2523991).sum := by decide
  have hdescent : baseEnd_2523991 < baseStart_2523991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2523991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524004 : List Nat := [2, 3, 1, 1, 4, 2, 1, 3, 1, 1, 4]
def baseStart_2524004 : Nat := 118140960795 + 2524004 * 2 ^ 59
def prefixEnd_2524004 : Nat := 4983230072969 + 3 ^ 40 * 2524004 * 2
def baseEnd_2524004 : Nat := 1296027225870848056442323

theorem tailTrace_2524004 : CollatzResearch.WordTrace tailWord_2524004 prefixEnd_2524004 1296027225870848056442323 := by
  unfold tailWord_2524004
  simp only [CollatzResearch.WordTrace]
  refine ⟨46028994373986024204713533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61371992498648032272951377 46028994373986024204713533)
  ·
    refine ⟨17260872890244759076767575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46028994373986024204713533 17260872890244759076767575)
    ·
      refine ⟨25891309335367138615151363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17260872890244759076767575 25891309335367138615151363)
      ·
        refine ⟨38836964003050707922727045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25891309335367138615151363 38836964003050707922727045)
        ·
          refine ⟨7281930750572007735511321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38836964003050707922727045 7281930750572007735511321)
          ·
            refine ⟨5461448062929005801633491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7281930750572007735511321 5461448062929005801633491)
            ·
              refine ⟨8192172094393508702450237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5461448062929005801633491 8192172094393508702450237)
              ·
                refine ⟨3072064535397565763418839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8192172094393508702450237 3072064535397565763418839)
                ·
                  refine ⟨4608096803096348645128259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3072064535397565763418839 4608096803096348645128259)
                  ·
                    refine ⟨6912145204644522967692389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4608096803096348645128259 6912145204644522967692389)
                    ·
                      refine ⟨1296027225870848056442323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6912145204644522967692389 1296027225870848056442323)
                      ·
                        rfl

theorem cell23_2524004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 3, 1, 1, 4].length) (baseStart_2524004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2524004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2524004 prefixEnd_2524004 := by exact prefixLift 2524004
  have htrace : WordTrace (prefixWord ++ tailWord_2524004) baseStart_2524004 baseEnd_2524004 := by
    simpa [prefixWord, tailWord_2524004, baseEnd_2524004] using wordTrace_append hprefix tailTrace_2524004
  have hstable : (prefixWord ++ tailWord_2524004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524004).length < 2 ^ (prefixWord ++ tailWord_2524004).sum := by decide
  have hdescent : baseEnd_2524004 < baseStart_2524004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524021 : List Nat := [1, 3, 4, 1, 1, 2, 1, 3, 3, 2, 2]
def baseStart_2524021 : Nat := 118140960795 + 2524021 * 2 ^ 59
def prefixEnd_2524021 : Nat := 4983230072969 + 3 ^ 40 * 2524021 * 2
def baseEnd_2524021 : Nat := 1296035955041974489929745

theorem tailTrace_2524021 : CollatzResearch.WordTrace tailWord_2524021 prefixEnd_2524021 1296035955041974489929745 := by
  unfold tailWord_2524021
  simp only [CollatzResearch.WordTrace]
  refine ⟨92058608788910460312795917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61372405859273640208530611 92058608788910460312795917)
  ·
    refine ⟨34521978295841422617298469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92058608788910460312795917 34521978295841422617298469)
    ·
      refine ⟨6472870930470266740743463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34521978295841422617298469 6472870930470266740743463)
      ·
        refine ⟨9709306395705400111115195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6472870930470266740743463 9709306395705400111115195)
        ·
          refine ⟨14563959593558100166672793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9709306395705400111115195 14563959593558100166672793)
          ·
            refine ⟨10922969695168575125004595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14563959593558100166672793 10922969695168575125004595)
            ·
              refine ⟨16384454542752862687506893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10922969695168575125004595 16384454542752862687506893)
              ·
                refine ⟨6144170453532323507815085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16384454542752862687506893 6144170453532323507815085)
                ·
                  refine ⟨2304063920074621315430657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6144170453532323507815085 2304063920074621315430657)
                  ·
                    refine ⟨1728047940055965986572993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2304063920074621315430657 1728047940055965986572993)
                    ·
                      refine ⟨1296035955041974489929745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1728047940055965986572993 1296035955041974489929745)
                      ·
                        rfl

theorem cell23_2524021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_2524021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2524021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2524021 prefixEnd_2524021 := by exact prefixLift 2524021
  have htrace : WordTrace (prefixWord ++ tailWord_2524021) baseStart_2524021 baseEnd_2524021 := by
    simpa [prefixWord, tailWord_2524021, baseEnd_2524021] using wordTrace_append hprefix tailTrace_2524021
  have hstable : (prefixWord ++ tailWord_2524021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524021).length < 2 ^ (prefixWord ++ tailWord_2524021).sum := by decide
  have hdescent : baseEnd_2524021 < baseStart_2524021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524088 : List Nat := [2, 1, 2, 1, 2, 6, 2, 1, 2, 1, 3]
def baseStart_2524088 : Nat := 118140960795 + 2524088 * 2 ^ 59
def prefixEnd_2524088 : Nat := 4983230072969 + 3 ^ 40 * 2524088 * 2
def baseEnd_2524088 : Nat := 1296070358245825727791937

theorem tailTrace_2524088 : CollatzResearch.WordTrace tailWord_2524088 prefixEnd_2524088 1296070358245825727791937 := by
  unfold tailWord_2524088
  simp only [CollatzResearch.WordTrace]
  refine ⟨46030526239833865377742459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61374034986445153836989945 46030526239833865377742459)
  ·
    refine ⟨69045789359750798066613689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46030526239833865377742459 69045789359750798066613689)
    ·
      refine ⟨51784342019813098549960267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69045789359750798066613689 51784342019813098549960267)
      ·
        refine ⟨77676513029719647824940401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51784342019813098549960267 77676513029719647824940401)
        ·
          refine ⟨58257384772289735868705301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77676513029719647824940401 58257384772289735868705301)
          ·
            refine ⟨2730814911201081368845561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 58257384772289735868705301 2730814911201081368845561)
            ·
              refine ⟨2048111183400811026634171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2730814911201081368845561 2048111183400811026634171)
              ·
                refine ⟨3072166775101216539951257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2048111183400811026634171 3072166775101216539951257)
                ·
                  refine ⟨2304125081325912404963443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3072166775101216539951257 2304125081325912404963443)
                  ·
                    refine ⟨3456187621988868607445165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2304125081325912404963443 3456187621988868607445165)
                    ·
                      refine ⟨1296070358245825727791937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3456187621988868607445165 1296070358245825727791937)
                      ·
                        rfl

theorem cell23_2524088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2, 1, 2, 1, 3].length) (baseStart_2524088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2524088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2524088 prefixEnd_2524088 := by exact prefixLift 2524088
  have htrace : WordTrace (prefixWord ++ tailWord_2524088) baseStart_2524088 baseEnd_2524088 := by
    simpa [prefixWord, tailWord_2524088, baseEnd_2524088] using wordTrace_append hprefix tailTrace_2524088
  have hstable : (prefixWord ++ tailWord_2524088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524088).length < 2 ^ (prefixWord ++ tailWord_2524088).sum := by decide
  have hdescent : baseEnd_2524088 < baseStart_2524088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524114 : List Nat := [3, 2, 2, 3, 1, 1, 2, 1, 2, 1, 5]
def baseStart_2524114 : Nat := 118140960795 + 2524114 * 2 ^ 59
def prefixEnd_2524114 : Nat := 4983230072969 + 3 ^ 40 * 2524114 * 2
def baseEnd_2524114 : Nat := 1296083708742842626066817

theorem tailTrace_2524114 : CollatzResearch.WordTrace tailWord_2524114 prefixEnd_2524114 1296083708742842626066817 := by
  unfold tailWord_2524114
  simp only [CollatzResearch.WordTrace]
  refine ⟨23015500194393384298982849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61374667185049024797287597 23015500194393384298982849)
  ·
    refine ⟨17261625145795038224237137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23015500194393384298982849 17261625145795038224237137)
    ·
      refine ⟨12946218859346278668177853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17261625145795038224237137 12946218859346278668177853)
      ·
        refine ⟨4854832072254854500566695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12946218859346278668177853 4854832072254854500566695)
        ·
          refine ⟨7282248108382281750850043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4854832072254854500566695 7282248108382281750850043)
          ·
            refine ⟨10923372162573422626275065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7282248108382281750850043 10923372162573422626275065)
            ·
              refine ⟨8192529121930066969706299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10923372162573422626275065 8192529121930066969706299)
              ·
                refine ⟨12288793682895100454559449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8192529121930066969706299 12288793682895100454559449)
                ·
                  refine ⟨9216595262171325340919587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12288793682895100454559449 9216595262171325340919587)
                  ·
                    refine ⟨13824892893256988011379381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9216595262171325340919587 13824892893256988011379381)
                    ·
                      refine ⟨1296083708742842626066817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13824892893256988011379381 1296083708742842626066817)
                      ·
                        rfl

theorem cell23_2524114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_2524114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2524114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2524114 prefixEnd_2524114 := by exact prefixLift 2524114
  have htrace : WordTrace (prefixWord ++ tailWord_2524114) baseStart_2524114 baseEnd_2524114 := by
    simpa [prefixWord, tailWord_2524114, baseEnd_2524114] using wordTrace_append hprefix tailTrace_2524114
  have hstable : (prefixWord ++ tailWord_2524114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524114).length < 2 ^ (prefixWord ++ tailWord_2524114).sum := by decide
  have hdescent : baseEnd_2524114 < baseStart_2524114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524197 : List Nat := [1, 3, 1, 2, 2, 2, 1, 2, 2, 1, 6]
def baseStart_2524197 : Nat := 118140960795 + 2524197 * 2 ^ 59
def prefixEnd_2524197 : Nat := 4983230072969 + 3 ^ 40 * 2524197 * 2
def baseEnd_2524197 : Nat := 1296126327637165801328935

theorem tailTrace_2524197 : CollatzResearch.WordTrace tailWord_2524197 prefixEnd_2524197 1296126327637165801328935 := by
  unfold tailWord_2524197
  simp only [CollatzResearch.WordTrace]
  refine ⟨92065028036272842371202845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61376685357515228247468563 92065028036272842371202845)
  ·
    refine ⟨34524385513602315889201067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92065028036272842371202845 34524385513602315889201067)
    ·
      refine ⟨51786578270403473833801601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34524385513602315889201067 51786578270403473833801601)
      ·
        refine ⟨38839933702802605375351201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51786578270403473833801601 38839933702802605375351201)
        ·
          refine ⟨29129950277101954031513401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38839933702802605375351201 29129950277101954031513401)
          ·
            refine ⟨21847462707826465523635051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29129950277101954031513401 21847462707826465523635051)
            ·
              refine ⟨32771194061739698285452577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21847462707826465523635051 32771194061739698285452577)
              ·
                refine ⟨24578395546304773714089433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32771194061739698285452577 24578395546304773714089433)
                ·
                  refine ⟨18433796659728580285567075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24578395546304773714089433 18433796659728580285567075)
                  ·
                    refine ⟨27650694989592870428350613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18433796659728580285567075 27650694989592870428350613)
                    ·
                      refine ⟨1296126327637165801328935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27650694989592870428350613 1296126327637165801328935)
                      ·
                        rfl

theorem cell23_2524197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_2524197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2524197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2524197 prefixEnd_2524197 := by exact prefixLift 2524197
  have htrace : WordTrace (prefixWord ++ tailWord_2524197) baseStart_2524197 baseEnd_2524197 := by
    simpa [prefixWord, tailWord_2524197, baseEnd_2524197] using wordTrace_append hprefix tailTrace_2524197
  have hstable : (prefixWord ++ tailWord_2524197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524197).length < 2 ^ (prefixWord ++ tailWord_2524197).sum := by decide
  have hdescent : baseEnd_2524197 < baseStart_2524197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524247 : List Nat := [1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 7]
def baseStart_2524247 : Nat := 118140960795 + 2524247 * 2 ^ 59
def prefixEnd_2524247 : Nat := 4983230072969 + 3 ^ 40 * 2524247 * 2
def baseEnd_2524247 : Nat := 1296152001669890605703705

theorem tailTrace_2524247 : CollatzResearch.WordTrace tailWord_2524247 prefixEnd_2524247 1296152001669890605703705 := by
  unfold tailWord_2524247
  simp only [CollatzResearch.WordTrace]
  refine ⟨92066851686091700910522995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61377901124061133940348663 92066851686091700910522995)
  ·
    refine ⟨138100277529137551365784493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92066851686091700910522995 138100277529137551365784493)
    ·
      refine ⟨51787604073426581762169185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138100277529137551365784493 51787604073426581762169185)
      ·
        refine ⟨38840703055069936321626889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51787604073426581762169185 38840703055069936321626889)
        ·
          refine ⟨29130527291302452241220167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38840703055069936321626889 29130527291302452241220167)
          ·
            refine ⟨43695790936953678361830251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29130527291302452241220167 43695790936953678361830251)
            ·
              refine ⟨65543686405430517542745377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43695790936953678361830251 65543686405430517542745377)
              ·
                refine ⟨49157764804072888157059033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65543686405430517542745377 49157764804072888157059033)
                ·
                  refine ⟨36868323603054666117794275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49157764804072888157059033 36868323603054666117794275)
                  ·
                    refine ⟨55302485404581999176691413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36868323603054666117794275 55302485404581999176691413)
                    ·
                      refine ⟨1296152001669890605703705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 55302485404581999176691413 1296152001669890605703705)
                      ·
                        rfl

theorem cell23_2524247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_2524247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2524247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2524247 prefixEnd_2524247 := by exact prefixLift 2524247
  have htrace : WordTrace (prefixWord ++ tailWord_2524247) baseStart_2524247 baseEnd_2524247 := by
    simpa [prefixWord, tailWord_2524247, baseEnd_2524247] using wordTrace_append hprefix tailTrace_2524247
  have hstable : (prefixWord ++ tailWord_2524247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524247).length < 2 ^ (prefixWord ++ tailWord_2524247).sum := by decide
  have hdescent : baseEnd_2524247 < baseStart_2524247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524258 : List Nat := [3, 3, 2, 2, 1, 1, 4, 1, 6]
def baseStart_2524258 : Nat := 118140960795 + 2524258 * 2 ^ 59
def prefixEnd_2524258 : Nat := 4983230072969 + 3 ^ 40 * 2524258 * 2
def baseEnd_2524258 : Nat := 144017516661898895851795

theorem tailTrace_2524258 : CollatzResearch.WordTrace tailWord_2524258 prefixEnd_2524258 144017516661898895851795 := by
  unfold tailWord_2524258
  simp only [CollatzResearch.WordTrace]
  refine ⟨23016813222262962447293357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61378168592701233192782285 23016813222262962447293357)
  ·
    refine ⟨8631304958348610917735009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23016813222262962447293357 8631304958348610917735009)
    ·
      refine ⟨6473478718761458188301257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8631304958348610917735009 6473478718761458188301257)
      ·
        refine ⟨4855109039071093641225943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6473478718761458188301257 4855109039071093641225943)
        ·
          refine ⟨7282663558606640461838915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4855109039071093641225943 7282663558606640461838915)
          ·
            refine ⟨10923995337909960692758373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7282663558606640461838915 10923995337909960692758373)
            ·
              refine ⟨2048249125858117629892195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10923995337909960692758373 2048249125858117629892195)
              ·
                refine ⟨3072373688787176444838293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2048249125858117629892195 3072373688787176444838293)
                ·
                  refine ⟨144017516661898895851795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3072373688787176444838293 144017516661898895851795)
                  ·
                    rfl

theorem cell23_2524258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4, 1, 6].length) (baseStart_2524258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2524258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2524258 prefixEnd_2524258 := by exact prefixLift 2524258
  have htrace : WordTrace (prefixWord ++ tailWord_2524258) baseStart_2524258 baseEnd_2524258 := by
    simpa [prefixWord, tailWord_2524258, baseEnd_2524258] using wordTrace_append hprefix tailTrace_2524258
  have hstable : (prefixWord ++ tailWord_2524258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524258).length < 2 ^ (prefixWord ++ tailWord_2524258).sum := by decide
  have hdescent : baseEnd_2524258 < baseStart_2524258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524261 : List Nat := [1, 3, 1, 3, 2, 1, 1, 2, 4, 3, 2]
def baseStart_2524261 : Nat := 118140960795 + 2524261 * 2 ^ 59
def prefixEnd_2524261 : Nat := 4983230072969 + 3 ^ 40 * 2524261 * 2
def baseEnd_2524261 : Nat := 1296159190399053550928641

theorem tailTrace_2524261 : CollatzResearch.WordTrace tailWord_2524261 prefixEnd_2524261 1296159190399053550928641 := by
  unfold tailWord_2524261
  simp only [CollatzResearch.WordTrace]
  refine ⟨92067362308040981301532637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61378241538693987534355091 92067362308040981301532637)
  ·
    refine ⟨34525260865515367988074739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92067362308040981301532637 34525260865515367988074739)
    ·
      refine ⟨51787891298273051982112109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34525260865515367988074739 51787891298273051982112109)
      ·
        refine ⟨19420459236852394493292041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51787891298273051982112109 19420459236852394493292041)
        ·
          refine ⟨14565344427639295869969031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19420459236852394493292041 14565344427639295869969031)
          ·
            refine ⟨21848016641458943804953547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14565344427639295869969031 21848016641458943804953547)
            ·
              refine ⟨32772024962188415707430321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21848016641458943804953547 32772024962188415707430321)
              ·
                refine ⟨24579018721641311780572741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32772024962188415707430321 24579018721641311780572741)
                ·
                  refine ⟨4608566010307745958857389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24579018721641311780572741 4608566010307745958857389)
                  ·
                    refine ⟨1728212253865404734571521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4608566010307745958857389 1728212253865404734571521)
                    ·
                      refine ⟨1296159190399053550928641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1728212253865404734571521 1296159190399053550928641)
                      ·
                        rfl

theorem cell23_2524261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 4, 3, 2].length) (baseStart_2524261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2524261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2524261 prefixEnd_2524261 := by exact prefixLift 2524261
  have htrace : WordTrace (prefixWord ++ tailWord_2524261) baseStart_2524261 baseEnd_2524261 := by
    simpa [prefixWord, tailWord_2524261, baseEnd_2524261] using wordTrace_append hprefix tailTrace_2524261
  have hstable : (prefixWord ++ tailWord_2524261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524261).length < 2 ^ (prefixWord ++ tailWord_2524261).sum := by decide
  have hdescent : baseEnd_2524261 < baseStart_2524261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524267 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 7, 6]
def baseStart_2524267 : Nat := 118140960795 + 2524267 * 2 ^ 59
def prefixEnd_2524267 : Nat := 4983230072969 + 3 ^ 40 * 2524267 * 2
def baseEnd_2524267 : Nat := 432054090427660175817871

theorem tailTrace_2524267 : CollatzResearch.WordTrace tailWord_2524267 prefixEnd_2524267 432054090427660175817871 := by
  unfold tailWord_2524267
  simp only [CollatzResearch.WordTrace]
  refine ⟨92067581146019244326251055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61378387430679496217500703 92067581146019244326251055)
  ·
    refine ⟨138101371719028866489376583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92067581146019244326251055 138101371719028866489376583)
    ·
      refine ⟨207152057578543299734064875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138101371719028866489376583 207152057578543299734064875)
      ·
        refine ⟨310728086367814949601097313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207152057578543299734064875 310728086367814949601097313)
        ·
          refine ⟨233046064775861212200822985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 310728086367814949601097313 233046064775861212200822985)
          ·
            refine ⟨174784548581895909150617239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 233046064775861212200822985 174784548581895909150617239)
            ·
              refine ⟨262176822872843863725925859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174784548581895909150617239 262176822872843863725925859)
              ·
                refine ⟨393265234309265795588888789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 262176822872843863725925859 393265234309265795588888789)
                ·
                  refine ⟨9217153929123417084114581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 393265234309265795588888789 9217153929123417084114581)
                  ·
                    refine ⟨432054090427660175817871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9217153929123417084114581 432054090427660175817871)
                    ·
                      rfl

theorem cell23_2524267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7, 6].length) (baseStart_2524267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2524267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2524267 prefixEnd_2524267 := by exact prefixLift 2524267
  have htrace : WordTrace (prefixWord ++ tailWord_2524267) baseStart_2524267 baseEnd_2524267 := by
    simpa [prefixWord, tailWord_2524267, baseEnd_2524267] using wordTrace_append hprefix tailTrace_2524267
  have hstable : (prefixWord ++ tailWord_2524267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524267).length < 2 ^ (prefixWord ++ tailWord_2524267).sum := by decide
  have hdescent : baseEnd_2524267 < baseStart_2524267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524284 : List Nat := [2, 2, 2, 1, 1, 3, 3, 2, 1, 6]
def baseStart_2524284 : Nat := 118140960795 + 2524284 * 2 ^ 59
def prefixEnd_2524284 : Nat := 4983230072969 + 3 ^ 40 * 2524284 * 2
def baseEnd_2524284 : Nat := 432057000151368986980345

theorem tailTrace_2524284 : CollatzResearch.WordTrace tailWord_2524284 prefixEnd_2524284 432057000151368986980345 := by
  unfold tailWord_2524284
  simp only [CollatzResearch.WordTrace]
  refine ⟨46034100593478828114809953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61378800791305104153079937 46034100593478828114809953)
  ·
    refine ⟨34525575445109121086107465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46034100593478828114809953 34525575445109121086107465)
    ·
      refine ⟨25894181583831840814580599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34525575445109121086107465 25894181583831840814580599)
      ·
        refine ⟨38841272375747761221870899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25894181583831840814580599 38841272375747761221870899)
        ·
          refine ⟨58261908563621641832806349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38841272375747761221870899 58261908563621641832806349)
          ·
            refine ⟨21848215711358115687302381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58261908563621641832806349 21848215711358115687302381)
            ·
              refine ⟨8193080891759293382738393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21848215711358115687302381 8193080891759293382738393)
              ·
                refine ⟨6144810668819470037053795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8193080891759293382738393 6144810668819470037053795)
                ·
                  refine ⟨9217216003229205055580693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6144810668819470037053795 9217216003229205055580693)
                  ·
                    refine ⟨432057000151368986980345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9217216003229205055580693 432057000151368986980345)
                    ·
                      rfl

theorem cell23_2524284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 2, 1, 6].length) (baseStart_2524284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2524284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2524284 prefixEnd_2524284 := by exact prefixLift 2524284
  have htrace : WordTrace (prefixWord ++ tailWord_2524284) baseStart_2524284 baseEnd_2524284 := by
    simpa [prefixWord, tailWord_2524284, baseEnd_2524284] using wordTrace_append hprefix tailTrace_2524284
  have hstable : (prefixWord ++ tailWord_2524284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524284).length < 2 ^ (prefixWord ++ tailWord_2524284).sum := by decide
  have hdescent : baseEnd_2524284 < baseStart_2524284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524287 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 6]
def baseStart_2524287 : Nat := 118140960795 + 2524287 * 2 ^ 59
def prefixEnd_2524287 : Nat := 4983230072969 + 3 ^ 40 * 2524287 * 2
def baseEnd_2524287 : Nat := 1296172540896070449203521

theorem tailTrace_2524287 : CollatzResearch.WordTrace tailWord_2524287 prefixEnd_2524287 1296172540896070449203521 := by
  unfold tailWord_2524287
  simp only [CollatzResearch.WordTrace]
  refine ⟨92068310605946787741979115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61378873737297858494652743 92068310605946787741979115)
  ·
    refine ⟨138102465908920181612968673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92068310605946787741979115 138102465908920181612968673)
    ·
      refine ⟨103576849431690136209726505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138102465908920181612968673 103576849431690136209726505)
      ·
        refine ⟨77682637073767602157294879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103576849431690136209726505 77682637073767602157294879)
        ·
          refine ⟨116523955610651403235942319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77682637073767602157294879 116523955610651403235942319)
          ·
            refine ⟨174785933415977104853913479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116523955610651403235942319 174785933415977104853913479)
            ·
              refine ⟨262178900123965657280870219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174785933415977104853913479 262178900123965657280870219)
              ·
                refine ⟨393268350185948485921305329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 262178900123965657280870219 393268350185948485921305329)
                ·
                  refine ⟨294951262639461364440978997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 393268350185948485921305329 294951262639461364440978997)
                  ·
                    refine ⟨27651680872449502916341781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 294951262639461364440978997 27651680872449502916341781)
                    ·
                      refine ⟨1296172540896070449203521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27651680872449502916341781 1296172540896070449203521)
                      ·
                        rfl

theorem cell23_2524287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 6].length) (baseStart_2524287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2524287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2524287 prefixEnd_2524287 := by exact prefixLift 2524287
  have htrace : WordTrace (prefixWord ++ tailWord_2524287) baseStart_2524287 baseEnd_2524287 := by
    simpa [prefixWord, tailWord_2524287, baseEnd_2524287] using wordTrace_append hprefix tailTrace_2524287
  have hstable : (prefixWord ++ tailWord_2524287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524287).length < 2 ^ (prefixWord ++ tailWord_2524287).sum := by decide
  have hdescent : baseEnd_2524287 < baseStart_2524287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524297 : List Nat := [1, 2, 1, 1, 4, 14]
def baseStart_2524297 : Nat := 118140960795 + 2524297 * 2 ^ 59
def prefixEnd_2524297 : Nat := 4983230072969 + 3 ^ 40 * 2524297 * 2
def baseEnd_2524297 : Nat := 5334064509064260946825

theorem tailTrace_2524297 : CollatzResearch.WordTrace tailWord_2524297 prefixEnd_2524297 5334064509064260946825 := by
  unfold tailWord_2524297
  simp only [CollatzResearch.WordTrace]
  refine ⟨92068675335910559449843145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61379116890607039633228763 92068675335910559449843145)
  ·
    refine ⟨69051506501932919587382359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92068675335910559449843145 69051506501932919587382359)
    ·
      refine ⟨103577259752899379381073539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69051506501932919587382359 103577259752899379381073539)
      ·
        refine ⟨155365889629349069071610309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103577259752899379381073539 155365889629349069071610309)
        ·
          refine ⟨29131104305502950450926933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 155365889629349069071610309 29131104305502950450926933)
          ·
            refine ⟨5334064509064260946825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 29131104305502950450926933 5334064509064260946825)
            ·
              rfl

theorem cell23_2524297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 14].length) (baseStart_2524297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2524297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2524297 prefixEnd_2524297 := by exact prefixLift 2524297
  have htrace : WordTrace (prefixWord ++ tailWord_2524297) baseStart_2524297 baseEnd_2524297 := by
    simpa [prefixWord, tailWord_2524297, baseEnd_2524297] using wordTrace_append hprefix tailTrace_2524297
  have hstable : (prefixWord ++ tailWord_2524297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524297).length < 2 ^ (prefixWord ++ tailWord_2524297).sum := by decide
  have hdescent : baseEnd_2524297 < baseStart_2524297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524302 : List Nat := [4, 1, 1, 3, 2, 1, 4, 2, 1, 1, 3]
def baseStart_2524302 : Nat := 118140960795 + 2524302 * 2 ^ 59
def prefixEnd_2524302 : Nat := 4983230072969 + 3 ^ 40 * 2524302 * 2
def baseEnd_2524302 : Nat := 1296180243105887890515953

theorem tailTrace_2524302 : CollatzResearch.WordTrace tailWord_2524302 prefixEnd_2524302 1296180243105887890515953 := by
  unfold tailWord_2524302
  simp only [CollatzResearch.WordTrace]
  refine ⟨11508607212611555662971895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61379238467261630202516773 11508607212611555662971895)
  ·
    refine ⟨17262910818917333494457843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11508607212611555662971895 17262910818917333494457843)
    ·
      refine ⟨25894366228376000241686765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17262910818917333494457843 25894366228376000241686765)
      ·
        refine ⟨9710387335641000090632537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25894366228376000241686765 9710387335641000090632537)
        ·
          refine ⟨7282790501730750067974403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9710387335641000090632537 7282790501730750067974403)
          ·
            refine ⟨10924185752596125101961605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7282790501730750067974403 10924185752596125101961605)
            ·
              refine ⟨2048284828611773456617801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10924185752596125101961605 2048284828611773456617801)
              ·
                refine ⟨1536213621458830092463351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2048284828611773456617801 1536213621458830092463351)
                ·
                  refine ⟨2304320432188245138695027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1536213621458830092463351 2304320432188245138695027)
                  ·
                    refine ⟨3456480648282367708042541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2304320432188245138695027 3456480648282367708042541)
                    ·
                      refine ⟨1296180243105887890515953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3456480648282367708042541 1296180243105887890515953)
                      ·
                        rfl

theorem cell23_2524302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_2524302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2524302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2524302 prefixEnd_2524302 := by exact prefixLift 2524302
  have htrace : WordTrace (prefixWord ++ tailWord_2524302) baseStart_2524302 baseEnd_2524302 := by
    simpa [prefixWord, tailWord_2524302, baseEnd_2524302] using wordTrace_append hprefix tailTrace_2524302
  have hstable : (prefixWord ++ tailWord_2524302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524302).length < 2 ^ (prefixWord ++ tailWord_2524302).sum := by decide
  have hdescent : baseEnd_2524302 < baseStart_2524302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524311 : List Nat := [1, 1, 3, 3, 3, 1, 1, 2, 3, 2, 3]
def baseStart_2524311 : Nat := 118140960795 + 2524311 * 2 ^ 59
def prefixEnd_2524311 : Nat := 4983230072969 + 3 ^ 40 * 2524311 * 2
def baseEnd_2524311 : Nat := 1296184864431778355303411

theorem tailTrace_2524311 : CollatzResearch.WordTrace tailWord_2524311 prefixEnd_2524311 1296184864431778355303411 := by
  unfold tailWord_2524311
  simp only [CollatzResearch.WordTrace]
  refine ⟨92069185957859839840852787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61379457305239893227235191 92069185957859839840852787)
  ·
    refine ⟨138103778936789759761279181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92069185957859839840852787 138103778936789759761279181)
    ·
      refine ⟨51788917101296159910479693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138103778936789759761279181 51788917101296159910479693)
      ·
        refine ⟨19420843912986059966429885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51788917101296159910479693 19420843912986059966429885)
        ·
          refine ⟨7282816467369772487411207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19420843912986059966429885 7282816467369772487411207)
          ·
            refine ⟨10924224701054658731116811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7282816467369772487411207 10924224701054658731116811)
            ·
              refine ⟨16386337051581988096675217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10924224701054658731116811 16386337051581988096675217)
              ·
                refine ⟨12289752788686491072506413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16386337051581988096675217 12289752788686491072506413)
                ·
                  refine ⟨4608657295757434152189905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12289752788686491072506413 4608657295757434152189905)
                  ·
                    refine ⟨3456492971818075614142429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4608657295757434152189905 3456492971818075614142429)
                    ·
                      refine ⟨1296184864431778355303411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3456492971818075614142429 1296184864431778355303411)
                      ·
                        rfl

theorem cell23_2524311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_2524311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2524311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2524311 prefixEnd_2524311 := by exact prefixLift 2524311
  have htrace : WordTrace (prefixWord ++ tailWord_2524311) baseStart_2524311 baseEnd_2524311 := by
    simpa [prefixWord, tailWord_2524311, baseEnd_2524311] using wordTrace_append hprefix tailTrace_2524311
  have hstable : (prefixWord ++ tailWord_2524311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524311).length < 2 ^ (prefixWord ++ tailWord_2524311).sum := by decide
  have hdescent : baseEnd_2524311 < baseStart_2524311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524318 : List Nat := [4, 3, 1, 1, 2, 2, 2, 1, 1, 6]
def baseStart_2524318 : Nat := 118140960795 + 2524318 * 2 ^ 59
def prefixEnd_2524318 : Nat := 4983230072969 + 3 ^ 40 * 2524318 * 2
def baseEnd_2524318 : Nat := 432062819598786609305293

theorem tailTrace_2524318 : CollatzResearch.WordTrace tailWord_2524318 prefixEnd_2524318 432062819598786609305293 := by
  unfold tailWord_2524318
  simp only [CollatzResearch.WordTrace]
  refine ⟨11508680158604310004544701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61379627512556320024238405 11508680158604310004544701)
  ·
    refine ⟨4315755059476616251704263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11508680158604310004544701 4315755059476616251704263)
    ·
      refine ⟨6473632589214924377556395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4315755059476616251704263 6473632589214924377556395)
      ·
        refine ⟨9710448883822386566334593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6473632589214924377556395 9710448883822386566334593)
        ·
          refine ⟨7282836662866789924750945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9710448883822386566334593 7282836662866789924750945)
          ·
            refine ⟨5462127497150092443563209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7282836662866789924750945 5462127497150092443563209)
            ·
              refine ⟨4096595622862569332672407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5462127497150092443563209 4096595622862569332672407)
              ·
                refine ⟨6144893434293853999008611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4096595622862569332672407 6144893434293853999008611)
                ·
                  refine ⟨9217340151440780998512917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6144893434293853999008611 9217340151440780998512917)
                  ·
                    refine ⟨432062819598786609305293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9217340151440780998512917 432062819598786609305293)
                    ·
                      rfl

theorem cell23_2524318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_2524318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2524318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2524318 prefixEnd_2524318 := by exact prefixLift 2524318
  have htrace : WordTrace (prefixWord ++ tailWord_2524318) baseStart_2524318 baseEnd_2524318 := by
    simpa [prefixWord, tailWord_2524318, baseEnd_2524318] using wordTrace_append hprefix tailTrace_2524318
  have hstable : (prefixWord ++ tailWord_2524318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524318).length < 2 ^ (prefixWord ++ tailWord_2524318).sum := by decide
  have hdescent : baseEnd_2524318 < baseStart_2524318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524321 : List Nat := [1, 2, 3, 3, 1, 1, 4, 1, 1, 2, 4]
def baseStart_2524321 : Nat := 118140960795 + 2524321 * 2 ^ 59
def prefixEnd_2524321 : Nat := 4983230072969 + 3 ^ 40 * 2524321 * 2
def baseEnd_2524321 : Nat := 1296189999238323316178365

theorem tailTrace_2524321 : CollatzResearch.WordTrace tailWord_2524321 prefixEnd_2524321 1296189999238323316178365 := by
  unfold tailWord_2524321
  simp only [CollatzResearch.WordTrace]
  refine ⟨92069550687823611548716817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61379700458549074365811211 92069550687823611548716817)
  ·
    refine ⟨69052163015867708661537613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92069550687823611548716817 69052163015867708661537613)
    ·
      refine ⟨25894561130950390748076605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69052163015867708661537613 25894561130950390748076605)
      ·
        refine ⟨9710460424106396530528727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25894561130950390748076605 9710460424106396530528727)
        ·
          refine ⟨14565690636159594795793091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9710460424106396530528727 14565690636159594795793091)
          ·
            refine ⟨21848535954239392193689637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14565690636159594795793091 21848535954239392193689637)
            ·
              refine ⟨4096600491419886036316807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21848535954239392193689637 4096600491419886036316807)
              ·
                refine ⟨6144900737129829054475211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4096600491419886036316807 6144900737129829054475211)
                ·
                  refine ⟨9217351105694743581712817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6144900737129829054475211 9217351105694743581712817)
                  ·
                    refine ⟨6913013329271057686284613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9217351105694743581712817 6913013329271057686284613)
                    ·
                      refine ⟨1296189999238323316178365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6913013329271057686284613 1296189999238323316178365)
                      ·
                        rfl

theorem cell23_2524321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_2524321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2524321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2524321 prefixEnd_2524321 := by exact prefixLift 2524321
  have htrace : WordTrace (prefixWord ++ tailWord_2524321) baseStart_2524321 baseEnd_2524321 := by
    simpa [prefixWord, tailWord_2524321, baseEnd_2524321] using wordTrace_append hprefix tailTrace_2524321
  have hstable : (prefixWord ++ tailWord_2524321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524321).length < 2 ^ (prefixWord ++ tailWord_2524321).sum := by decide
  have hdescent : baseEnd_2524321 < baseStart_2524321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524342 : List Nat := [5, 1, 3, 2, 1, 1, 1, 3, 1, 1, 4]
def baseStart_2524342 : Nat := 118140960795 + 2524342 * 2 ^ 59
def prefixEnd_2524342 : Nat := 4983230072969 + 3 ^ 40 * 2524342 * 2
def baseEnd_2524342 : Nat := 1296200782332067734015769

theorem tailTrace_2524342 : CollatzResearch.WordTrace tailWord_2524342 prefixEnd_2524342 1296200782332067734015769 := by
  unfold tailWord_2524342
  simp only [CollatzResearch.WordTrace]
  refine ⟨5754394788796720758451955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61380211080498354756820853 5754394788796720758451955)
  ·
    refine ⟨8631592183195081137677933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5754394788796720758451955 8631592183195081137677933)
    ·
      refine ⟨3236847068698155426629225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8631592183195081137677933 3236847068698155426629225)
      ·
        refine ⟨2427635301523616569971919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3236847068698155426629225 2427635301523616569971919)
        ·
          refine ⟨3641452952285424854957879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2427635301523616569971919 3641452952285424854957879)
          ·
            refine ⟨5462179428428137282436819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3641452952285424854957879 5462179428428137282436819)
            ·
              refine ⟨8193269142642205923655229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5462179428428137282436819 8193269142642205923655229)
              ·
                refine ⟨3072475928490827221370711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8193269142642205923655229 3072475928490827221370711)
                ·
                  refine ⟨4608713892736240832056067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3072475928490827221370711 4608713892736240832056067)
                  ·
                    refine ⟨6913070839104361248084101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4608713892736240832056067 6913070839104361248084101)
                    ·
                      refine ⟨1296200782332067734015769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6913070839104361248084101 1296200782332067734015769)
                      ·
                        rfl

theorem cell23_2524342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_2524342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2524342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2524342 prefixEnd_2524342 := by exact prefixLift 2524342
  have htrace : WordTrace (prefixWord ++ tailWord_2524342) baseStart_2524342 baseEnd_2524342 := by
    simpa [prefixWord, tailWord_2524342, baseEnd_2524342] using wordTrace_append hprefix tailTrace_2524342
  have hstable : (prefixWord ++ tailWord_2524342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524342).length < 2 ^ (prefixWord ++ tailWord_2524342).sum := by decide
  have hdescent : baseEnd_2524342 < baseStart_2524342 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524345 : List Nat := [1, 2, 1, 4, 1, 5, 2, 1, 1, 2, 3]
def baseStart_2524345 : Nat := 118140960795 + 2524345 * 2 ^ 59
def prefixEnd_2524345 : Nat := 4983230072969 + 3 ^ 40 * 2524345 * 2
def baseEnd_2524345 : Nat := 1296202322774031222278255

theorem tailTrace_2524345 : CollatzResearch.WordTrace tailWord_2524345 prefixEnd_2524345 1296202322774031222278255 := by
  unfold tailWord_2524345
  simp only [CollatzResearch.WordTrace]
  refine ⟨92070426039736663647590489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61380284026491109098393659 92070426039736663647590489)
  ·
    refine ⟨69052819529802497735692867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92070426039736663647590489 69052819529802497735692867)
    ·
      refine ⟨103579229294703746603539301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69052819529802497735692867 103579229294703746603539301)
      ·
        refine ⟨19421105492756952488163619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103579229294703746603539301 19421105492756952488163619)
        ·
          refine ⟨29131658239135428732245429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19421105492756952488163619 29131658239135428732245429)
          ·
            refine ⟨2731092959918946443648009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29131658239135428732245429 2731092959918946443648009)
            ·
              refine ⟨2048319719939209832736007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2731092959918946443648009 2048319719939209832736007)
              ·
                refine ⟨3072479579908814749104011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2048319719939209832736007 3072479579908814749104011)
                ·
                  refine ⟨4608719369863222123656017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3072479579908814749104011 4608719369863222123656017)
                  ·
                    refine ⟨3456539527397416592742013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4608719369863222123656017 3456539527397416592742013)
                    ·
                      refine ⟨1296202322774031222278255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3456539527397416592742013 1296202322774031222278255)
                      ·
                        rfl

theorem cell23_2524345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2, 1, 1, 2, 3].length) (baseStart_2524345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2524345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2524345 prefixEnd_2524345 := by exact prefixLift 2524345
  have htrace : WordTrace (prefixWord ++ tailWord_2524345) baseStart_2524345 baseEnd_2524345 := by
    simpa [prefixWord, tailWord_2524345, baseEnd_2524345] using wordTrace_append hprefix tailTrace_2524345
  have hstable : (prefixWord ++ tailWord_2524345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524345).length < 2 ^ (prefixWord ++ tailWord_2524345).sum := by decide
  have hdescent : baseEnd_2524345 < baseStart_2524345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524372 : List Nat := [2, 4, 1, 4, 2, 1, 1, 1, 1, 2, 4]
def baseStart_2524372 : Nat := 118140960795 + 2524372 * 2 ^ 59
def prefixEnd_2524372 : Nat := 4983230072969 + 3 ^ 40 * 2524372 * 2
def baseEnd_2524372 : Nat := 1296216186751702616640631

theorem tailTrace_2524372 : CollatzResearch.WordTrace tailWord_2524372 prefixEnd_2524372 1296216186751702616640631 := by
  unfold tailWord_2524372
  simp only [CollatzResearch.WordTrace]
  refine ⟨46035705405319423629411685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61380940540425898172548913 46035705405319423629411685)
  ·
    refine ⟨8631694763497391930514691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46035705405319423629411685 8631694763497391930514691)
    ·
      refine ⟨12947542145246087895772037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8631694763497391930514691 12947542145246087895772037)
      ·
        refine ⟨2427664152233641480457257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12947542145246087895772037 2427664152233641480457257)
        ·
          refine ⟨1820748114175231110342943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2427664152233641480457257 1820748114175231110342943)
          ·
            refine ⟨2731122171262846665514415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1820748114175231110342943 2731122171262846665514415)
            ·
              refine ⟨4096683256894269998271623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2731122171262846665514415 4096683256894269998271623)
              ·
                refine ⟨6145024885341404997407435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4096683256894269998271623 6145024885341404997407435)
                ·
                  refine ⟨9217537328012107496111153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6145024885341404997407435 9217537328012107496111153)
                  ·
                    refine ⟨6913152996009080622083365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9217537328012107496111153 6913152996009080622083365)
                    ·
                      refine ⟨1296216186751702616640631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6913152996009080622083365 1296216186751702616640631)
                      ·
                        rfl

theorem cell23_2524372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_2524372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2524372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2524372 prefixEnd_2524372 := by exact prefixLift 2524372
  have htrace : WordTrace (prefixWord ++ tailWord_2524372) baseStart_2524372 baseEnd_2524372 := by
    simpa [prefixWord, tailWord_2524372, baseEnd_2524372] using wordTrace_append hprefix tailTrace_2524372
  have hstable : (prefixWord ++ tailWord_2524372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524372).length < 2 ^ (prefixWord ++ tailWord_2524372).sum := by decide
  have hdescent : baseEnd_2524372 < baseStart_2524372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524385 : List Nat := [1, 2, 3, 1, 3, 3, 2, 2, 1, 3, 2]
def baseStart_2524385 : Nat := 118140960795 + 2524385 * 2 ^ 59
def prefixEnd_2524385 : Nat := 4983230072969 + 3 ^ 40 * 2524385 * 2
def baseEnd_2524385 : Nat := 1296222862000211065778071

theorem tailTrace_2524385 : CollatzResearch.WordTrace tailWord_2524385 prefixEnd_2524385 1296222862000211065778071 := by
  unfold tailWord_2524385
  simp only [CollatzResearch.WordTrace]
  refine ⟨92071884959591750479046609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61381256639727833652697739 92071884959591750479046609)
  ·
    refine ⟨69053913719693812859284957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92071884959591750479046609 69053913719693812859284957)
    ·
      refine ⟨25895217644885179822231859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69053913719693812859284957 25895217644885179822231859)
      ·
        refine ⟨38842826467327769733347789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25895217644885179822231859 38842826467327769733347789)
        ·
          refine ⟨14566059925247913650005421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38842826467327769733347789 14566059925247913650005421)
          ·
            refine ⟨5462272471967967618752033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14566059925247913650005421 5462272471967967618752033)
            ·
              refine ⟨4096704353975975714064025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5462272471967967618752033 4096704353975975714064025)
              ·
                refine ⟨3072528265481981785548019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4096704353975975714064025 3072528265481981785548019)
                ·
                  refine ⟨4608792398222972678322029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3072528265481981785548019 4608792398222972678322029)
                  ·
                    refine ⟨1728297149333614754370761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4608792398222972678322029 1728297149333614754370761)
                    ·
                      refine ⟨1296222862000211065778071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1728297149333614754370761 1296222862000211065778071)
                      ·
                        rfl

theorem cell23_2524385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 2, 1, 3, 2].length) (baseStart_2524385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2524385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2524385 prefixEnd_2524385 := by exact prefixLift 2524385
  have htrace : WordTrace (prefixWord ++ tailWord_2524385) baseStart_2524385 baseEnd_2524385 := by
    simpa [prefixWord, tailWord_2524385, baseEnd_2524385] using wordTrace_append hprefix tailTrace_2524385
  have hstable : (prefixWord ++ tailWord_2524385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524385).length < 2 ^ (prefixWord ++ tailWord_2524385).sum := by decide
  have hdescent : baseEnd_2524385 < baseStart_2524385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524398 : List Nat := [4, 1, 2, 1, 1, 1, 2, 4, 1, 4, 2]
def baseStart_2524398 : Nat := 118140960795 + 2524398 * 2 ^ 59
def prefixEnd_2524398 : Nat := 4983230072969 + 3 ^ 40 * 2524398 * 2
def baseEnd_2524398 : Nat := 1296229537248719514915511

theorem tailTrace_2524398 : CollatzResearch.WordTrace tailWord_2524398 prefixEnd_2524398 1296229537248719514915511 := by
  unfold tailWord_2524398
  simp only [CollatzResearch.WordTrace]
  refine ⟨11509044888568081712408731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61381572739029769132846565 11509044888568081712408731)
  ·
    refine ⟨17263567332852122568613097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11509044888568081712408731 17263567332852122568613097)
    ·
      refine ⟨12947675499639091926459823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17263567332852122568613097 12947675499639091926459823)
      ·
        refine ⟨19421513249458637889689735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12947675499639091926459823 19421513249458637889689735)
        ·
          refine ⟨29132269874187956834534603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19421513249458637889689735 29132269874187956834534603)
          ·
            refine ⟨43698404811281935251801905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29132269874187956834534603 43698404811281935251801905)
            ·
              refine ⟨32773803608461451438851429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43698404811281935251801905 32773803608461451438851429)
              ·
                refine ⟨6145088176586522144784643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32773803608461451438851429 6145088176586522144784643)
                ·
                  refine ⟨9217632264879783217176965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6145088176586522144784643 9217632264879783217176965)
                  ·
                    refine ⟨1728306049664959353220681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9217632264879783217176965 1728306049664959353220681)
                    ·
                      refine ⟨1296229537248719514915511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1728306049664959353220681 1296229537248719514915511)
                      ·
                        rfl

theorem cell23_2524398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 4, 1, 4, 2].length) (baseStart_2524398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2524398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2524398 prefixEnd_2524398 := by exact prefixLift 2524398
  have htrace : WordTrace (prefixWord ++ tailWord_2524398) baseStart_2524398 baseEnd_2524398 := by
    simpa [prefixWord, tailWord_2524398, baseEnd_2524398] using wordTrace_append hprefix tailTrace_2524398
  have hstable : (prefixWord ++ tailWord_2524398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524398).length < 2 ^ (prefixWord ++ tailWord_2524398).sum := by decide
  have hdescent : baseEnd_2524398 < baseStart_2524398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524451 : List Nat := [1, 1, 1, 4, 2, 3, 1, 3, 2, 5]
def baseStart_2524451 : Nat := 118140960795 + 2524451 * 2 ^ 59
def prefixEnd_2524451 : Nat := 4983230072969 + 3 ^ 40 * 2524451 * 2
def baseEnd_2524451 : Nat := 432085583907802602517589

theorem tailTrace_2524451 : CollatzResearch.WordTrace tailWord_2524451 prefixEnd_2524451 432085583907802602517589 := by
  unfold tailWord_2524451
  simp only [CollatzResearch.WordTrace]
  refine ⟨92074292177352643750949207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61382861451568429167299471 92074292177352643750949207)
  ·
    refine ⟨138111438266028965626423811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92074292177352643750949207 138111438266028965626423811)
    ·
      refine ⟨207167157399043448439635717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138111438266028965626423811 207167157399043448439635717)
      ·
        refine ⟨38843842012320646582431697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 207167157399043448439635717 38843842012320646582431697)
        ·
          refine ⟨29132881509240484936823773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38843842012320646582431697 29132881509240484936823773)
          ·
            refine ⟨10924830565965181851308915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29132881509240484936823773 10924830565965181851308915)
            ·
              refine ⟨16387245848947772776963373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10924830565965181851308915 16387245848947772776963373)
              ·
                refine ⟨6145217193355414791361265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16387245848947772776963373 6145217193355414791361265)
                ·
                  refine ⟨4608912895016561093520949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6145217193355414791361265 4608912895016561093520949)
                  ·
                    refine ⟨432085583907802602517589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4608912895016561093520949 432085583907802602517589)
                    ·
                      rfl

theorem cell23_2524451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 3, 2, 5].length) (baseStart_2524451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2524451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2524451 prefixEnd_2524451 := by exact prefixLift 2524451
  have htrace : WordTrace (prefixWord ++ tailWord_2524451) baseStart_2524451 baseEnd_2524451 := by
    simpa [prefixWord, tailWord_2524451, baseEnd_2524451] using wordTrace_append hprefix tailTrace_2524451
  have hstable : (prefixWord ++ tailWord_2524451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524451).length < 2 ^ (prefixWord ++ tailWord_2524451).sum := by decide
  have hdescent : baseEnd_2524451 < baseStart_2524451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524468 : List Nat := [2, 5, 1, 1, 1, 1, 1, 4, 2, 5]
def baseStart_2524468 : Nat := 118140960795 + 2524468 * 2 ^ 59
def prefixEnd_2524468 : Nat := 4983230072969 + 3 ^ 40 * 2524468 * 2
def baseEnd_2524468 : Nat := 432088493631511413680063

theorem tailTrace_2524468 : CollatzResearch.WordTrace tailWord_2524468 prefixEnd_2524468 432088493631511413680063 := by
  unfold tailWord_2524468
  simp only [CollatzResearch.WordTrace]
  refine ⟨46037456109145527827159029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61383274812194037102878705 46037456109145527827159029)
  ·
    refine ⟨4316011510232393233796159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46037456109145527827159029 4316011510232393233796159)
    ·
      refine ⟨6474017265348589850694239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4316011510232393233796159 6474017265348589850694239)
      ·
        refine ⟨9711025898022884776041359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6474017265348589850694239 9711025898022884776041359)
        ·
          refine ⟨14566538847034327164062039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9711025898022884776041359 14566538847034327164062039)
          ·
            refine ⟨21849808270551490746093059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14566538847034327164062039 21849808270551490746093059)
            ·
              refine ⟨32774712405827236119139589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21849808270551490746093059 32774712405827236119139589)
              ·
                refine ⟨6145258576092606772338673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32774712405827236119139589 6145258576092606772338673)
                ·
                  refine ⟨4608943932069455079254005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6145258576092606772338673 4608943932069455079254005)
                  ·
                    refine ⟨432088493631511413680063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4608943932069455079254005 432088493631511413680063)
                    ·
                      rfl

theorem cell23_2524468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_2524468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2524468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2524468 prefixEnd_2524468 := by exact prefixLift 2524468
  have htrace : WordTrace (prefixWord ++ tailWord_2524468) baseStart_2524468 baseEnd_2524468 := by
    simpa [prefixWord, tailWord_2524468, baseEnd_2524468] using wordTrace_append hprefix tailTrace_2524468
  have hstable : (prefixWord ++ tailWord_2524468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524468).length < 2 ^ (prefixWord ++ tailWord_2524468).sum := by decide
  have hdescent : baseEnd_2524468 < baseStart_2524468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524515 : List Nat := [1, 1, 1, 5, 2, 2, 1, 5, 1, 4]
def baseStart_2524515 : Nat := 118140960795 + 2524515 * 2 ^ 59
def prefixEnd_2524515 : Nat := 4983230072969 + 3 ^ 40 * 2524515 * 2
def baseEnd_2524515 : Nat := 432096538161765185717491

theorem tailTrace_2524515 : CollatzResearch.WordTrace tailWord_2524515 prefixEnd_2524515 432096538161765185717491 := by
  unfold tailWord_2524515
  simp only [CollatzResearch.WordTrace]
  refine ⟨92076626449120782681278999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61384417632747188454185999 92076626449120782681278999)
  ·
    refine ⟨138114939673681174021918499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92076626449120782681278999 138114939673681174021918499)
    ·
      refine ⟨207172409510521761032877749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138114939673681174021918499 207172409510521761032877749)
      ·
        refine ⟨19422413391611415096832289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 207172409510521761032877749 19422413391611415096832289)
        ·
          refine ⟨14566810043708561322624217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19422413391611415096832289 14566810043708561322624217)
          ·
            refine ⟨10925107532781420991968163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14566810043708561322624217 10925107532781420991968163)
            ·
              refine ⟨16387661299172131487952245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10925107532781420991968163 16387661299172131487952245)
              ·
                refine ⟨1536343246797387326995523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16387661299172131487952245 1536343246797387326995523)
                ·
                  refine ⟨2304514870196080990493285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1536343246797387326995523 2304514870196080990493285)
                  ·
                    refine ⟨432096538161765185717491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2304514870196080990493285 432096538161765185717491)
                    ·
                      rfl

theorem cell23_2524515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 5, 1, 4].length) (baseStart_2524515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2524515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2524515 prefixEnd_2524515 := by exact prefixLift 2524515
  have htrace : WordTrace (prefixWord ++ tailWord_2524515) baseStart_2524515 baseEnd_2524515 := by
    simpa [prefixWord, tailWord_2524515, baseEnd_2524515] using wordTrace_append hprefix tailTrace_2524515
  have hstable : (prefixWord ++ tailWord_2524515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524515).length < 2 ^ (prefixWord ++ tailWord_2524515).sum := by decide
  have hdescent : baseEnd_2524515 < baseStart_2524515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524538 : List Nat := [3, 1, 1, 1, 1, 1, 2, 2, 7, 1, 3]
def baseStart_2524538 : Nat := 118140960795 + 2524538 * 2 ^ 59
def prefixEnd_2524538 : Nat := 4983230072969 + 3 ^ 40 * 2524538 * 2
def baseEnd_2524538 : Nat := 1296301424540348967164867

theorem tailTrace_2524538 : CollatzResearch.WordTrace tailWord_2524538 prefixEnd_2524538 1296301424540348967164867 := by
  unfold tailWord_2524538
  simp only [CollatzResearch.WordTrace]
  refine ⟨23019366332009364402341567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61384976885358305072910845 23019366332009364402341567)
  ·
    refine ⟨34529049498014046603512351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23019366332009364402341567 34529049498014046603512351)
    ·
      refine ⟨51793574247021069905268527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34529049498014046603512351 51793574247021069905268527)
      ·
        refine ⟨77690361370531604857902791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51793574247021069905268527 77690361370531604857902791)
        ·
          refine ⟨116535542055797407286854187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77690361370531604857902791 116535542055797407286854187)
          ·
            refine ⟨174803313083696110930281281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116535542055797407286854187 174803313083696110930281281)
            ·
              refine ⟨131102484812772083197710961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 174803313083696110930281281 131102484812772083197710961)
              ·
                refine ⟨98326863609579062398283221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131102484812772083197710961 98326863609579062398283221)
                ·
                  refine ⟨2304535865849509274959763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 98326863609579062398283221 2304535865849509274959763)
                  ·
                    refine ⟨3456803798774263912439645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2304535865849509274959763 3456803798774263912439645)
                    ·
                      refine ⟨1296301424540348967164867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3456803798774263912439645 1296301424540348967164867)
                      ·
                        rfl

theorem cell23_2524538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 7, 1, 3].length) (baseStart_2524538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2524538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2524538 prefixEnd_2524538 := by exact prefixLift 2524538
  have htrace : WordTrace (prefixWord ++ tailWord_2524538) baseStart_2524538 baseEnd_2524538 := by
    simpa [prefixWord, tailWord_2524538, baseEnd_2524538] using wordTrace_append hprefix tailTrace_2524538
  have hstable : (prefixWord ++ tailWord_2524538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524538).length < 2 ^ (prefixWord ++ tailWord_2524538).sum := by decide
  have hdescent : baseEnd_2524538 < baseStart_2524538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524588 : List Nat := [2, 2, 1, 1, 1, 1, 6, 1, 4, 4]
def baseStart_2524588 : Nat := 118140960795 + 2524588 * 2 ^ 59
def prefixEnd_2524588 : Nat := 4983230072969 + 3 ^ 40 * 2524588 * 2
def baseEnd_2524588 : Nat := 432109032857691257179879

theorem tailTrace_2524588 : CollatzResearch.WordTrace tailWord_2524588 prefixEnd_2524588 432109032857691257179879 := by
  unfold tailWord_2524588
  simp only [CollatzResearch.WordTrace]
  refine ⟨46039644488928158074343209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61386192651904210765790945 46039644488928158074343209)
  ·
    refine ⟨34529733366696118555757407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46039644488928158074343209 34529733366696118555757407)
    ·
      refine ⟨51794600050044177833636111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34529733366696118555757407 51794600050044177833636111)
      ·
        refine ⟨77691900075066266750454167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51794600050044177833636111 77691900075066266750454167)
        ·
          refine ⟨116537850112599400125681251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77691900075066266750454167 116537850112599400125681251)
          ·
            refine ⟨174806775168899100188521877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116537850112599400125681251 174806775168899100188521877)
            ·
              refine ⟨8194067586042145321336963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 174806775168899100188521877 8194067586042145321336963)
              ·
                refine ⟨12291101379063217982005445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8194067586042145321336963 12291101379063217982005445)
                ·
                  refine ⟨2304581508574353371626021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12291101379063217982005445 2304581508574353371626021)
                  ·
                    refine ⟨432109032857691257179879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2304581508574353371626021 432109032857691257179879)
                    ·
                      rfl

theorem cell23_2524588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 4].length) (baseStart_2524588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2524588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2524588 prefixEnd_2524588 := by exact prefixLift 2524588
  have htrace : WordTrace (prefixWord ++ tailWord_2524588) baseStart_2524588 baseEnd_2524588 := by
    simpa [prefixWord, tailWord_2524588, baseEnd_2524588] using wordTrace_append hprefix tailTrace_2524588
  have hstable : (prefixWord ++ tailWord_2524588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524588).length < 2 ^ (prefixWord ++ tailWord_2524588).sum := by decide
  have hdescent : baseEnd_2524588 < baseStart_2524588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524589 : List Nat := [1, 5, 2, 2, 1, 3, 1, 1, 3, 1, 3]
def baseStart_2524589 : Nat := 118140960795 + 2524589 * 2 ^ 59
def prefixEnd_2524589 : Nat := 4983230072969 + 3 ^ 40 * 2524589 * 2
def baseEnd_2524589 : Nat := 1296327612053728267627133

theorem tailTrace_2524589 : CollatzResearch.WordTrace tailWord_2524589 prefixEnd_2524589 1296327612053728267627133 := by
  unfold tailWord_2524589
  simp only [CollatzResearch.WordTrace]
  refine ⟨92079325450852693319472821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61386216967235128879648547 92079325450852693319472821)
  ·
    refine ⟨8632436761017439998700577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 92079325450852693319472821 8632436761017439998700577)
    ·
      refine ⟨6474327570763079999025433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8632436761017439998700577 6474327570763079999025433)
      ·
        refine ⟨4855745678072309999269075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6474327570763079999025433 4855745678072309999269075)
        ·
          refine ⟨7283618517108464998903613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4855745678072309999269075 7283618517108464998903613)
          ·
            refine ⟨2731356943915674374588855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7283618517108464998903613 2731356943915674374588855)
            ·
              refine ⟨4097035415873511561883283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2731356943915674374588855 4097035415873511561883283)
              ·
                refine ⟨6145553123810267342824925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4097035415873511561883283 6145553123810267342824925)
                ·
                  refine ⟨2304582421428850253559347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6145553123810267342824925 2304582421428850253559347)
                  ·
                    refine ⟨3456873632143275380339021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2304582421428850253559347 3456873632143275380339021)
                    ·
                      refine ⟨1296327612053728267627133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3456873632143275380339021 1296327612053728267627133)
                      ·
                        rfl

theorem cell23_2524589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_2524589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2524589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2524589 prefixEnd_2524589 := by exact prefixLift 2524589
  have htrace : WordTrace (prefixWord ++ tailWord_2524589) baseStart_2524589 baseEnd_2524589 := by
    simpa [prefixWord, tailWord_2524589, baseEnd_2524589] using wordTrace_append hprefix tailTrace_2524589
  have hstable : (prefixWord ++ tailWord_2524589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524589).length < 2 ^ (prefixWord ++ tailWord_2524589).sum := by decide
  have hdescent : baseEnd_2524589 < baseStart_2524589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524605 : List Nat := [1, 4, 1, 2, 2, 1, 3, 3, 2, 4]
def baseStart_2524605 : Nat := 118140960795 + 2524605 * 2 ^ 59
def prefixEnd_2524605 : Nat := 4983230072969 + 3 ^ 40 * 2524605 * 2
def baseEnd_2524605 : Nat := 432111942581400068342353

theorem tailTrace_2524605 : CollatzResearch.WordTrace tailWord_2524605 prefixEnd_2524605 432111942581400068342353 := by
  unfold tailWord_2524605
  simp only [CollatzResearch.WordTrace]
  refine ⟨92079909018794728052055269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61386606012529818701370179 92079909018794728052055269)
  ·
    refine ⟨17264982941024011509760363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92079909018794728052055269 17264982941024011509760363)
    ·
      refine ⟨25897474411536017264640545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17264982941024011509760363 25897474411536017264640545)
      ·
        refine ⟨19423105808652012948480409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25897474411536017264640545 19423105808652012948480409)
        ·
          refine ⟨14567329356489009711360307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19423105808652012948480409 14567329356489009711360307)
          ·
            refine ⟨21850994034733514567040461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14567329356489009711360307 21850994034733514567040461)
            ·
              refine ⟨8194122763025067962640173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21850994034733514567040461 8194122763025067962640173)
              ·
                refine ⟨3072796036134400485990065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8194122763025067962640173 3072796036134400485990065)
                ·
                  refine ⟨2304597027100800364492549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3072796036134400485990065 2304597027100800364492549)
                  ·
                    refine ⟨432111942581400068342353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2304597027100800364492549 432111942581400068342353)
                    ·
                      rfl

theorem cell23_2524605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 3, 2, 4].length) (baseStart_2524605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2524605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2524605 prefixEnd_2524605 := by exact prefixLift 2524605
  have htrace : WordTrace (prefixWord ++ tailWord_2524605) baseStart_2524605 baseEnd_2524605 := by
    simpa [prefixWord, tailWord_2524605, baseEnd_2524605] using wordTrace_append hprefix tailTrace_2524605
  have hstable : (prefixWord ++ tailWord_2524605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524605).length < 2 ^ (prefixWord ++ tailWord_2524605).sum := by decide
  have hdescent : baseEnd_2524605 < baseStart_2524605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524612 : List Nat := [2, 3, 3, 2, 1, 1, 3, 2, 1, 1, 4]
def baseStart_2524612 : Nat := 118140960795 + 2524612 * 2 ^ 59
def prefixEnd_2524612 : Nat := 4983230072969 + 3 ^ 40 * 2524612 * 2
def baseEnd_2524612 : Nat := 1296339422108781677639527

theorem tailTrace_2524612 : CollatzResearch.WordTrace tailWord_2524612 prefixEnd_2524612 1296339422108781677639527 := by
  unfold tailWord_2524612
  simp only [CollatzResearch.WordTrace]
  refine ⟨46040082164884684123780045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61386776219846245498373393 46040082164884684123780045)
  ·
    refine ⟨17265030811831756546417517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46040082164884684123780045 17265030811831756546417517)
    ·
      refine ⟨6474386554436908704906569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17265030811831756546417517 6474386554436908704906569)
      ·
        refine ⟨4855789915827681528679927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6474386554436908704906569 4855789915827681528679927)
        ·
          refine ⟨7283684873741522293019891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4855789915827681528679927 7283684873741522293019891)
          ·
            refine ⟨10925527310612283439529837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7283684873741522293019891 10925527310612283439529837)
            ·
              refine ⟨4097072741479606289823689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10925527310612283439529837 4097072741479606289823689)
              ·
                refine ⟨3072804556109704717367767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4097072741479606289823689 3072804556109704717367767)
                ·
                  refine ⟨4609206834164557076051651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3072804556109704717367767 4609206834164557076051651)
                  ·
                    refine ⟨6913810251246835614077477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4609206834164557076051651 6913810251246835614077477)
                    ·
                      refine ⟨1296339422108781677639527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6913810251246835614077477 1296339422108781677639527)
                      ·
                        rfl

theorem cell23_2524612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_2524612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2524612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2524612 prefixEnd_2524612 := by exact prefixLift 2524612
  have htrace : WordTrace (prefixWord ++ tailWord_2524612) baseStart_2524612 baseEnd_2524612 := by
    simpa [prefixWord, tailWord_2524612, baseEnd_2524612] using wordTrace_append hprefix tailTrace_2524612
  have hstable : (prefixWord ++ tailWord_2524612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524612).length < 2 ^ (prefixWord ++ tailWord_2524612).sum := by decide
  have hdescent : baseEnd_2524612 < baseStart_2524612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524629 : List Nat := [1, 3, 2, 3, 1, 1, 2, 5, 1, 2, 2]
def baseStart_2524629 : Nat := 118140960795 + 2524629 * 2 ^ 59
def prefixEnd_2524629 : Nat := 4983230072969 + 3 ^ 40 * 2524629 * 2
def baseEnd_2524629 : Nat := 1296348151279908111126949

theorem tailTrace_2524629 : CollatzResearch.WordTrace tailWord_2524629 prefixEnd_2524629 1296348151279908111126949 := by
  unfold tailWord_2524629
  simp only [CollatzResearch.WordTrace]
  refine ⟨92080784370707780150928941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61387189580471853433952627 92080784370707780150928941)
  ·
    refine ⟨34530294139015417556598353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92080784370707780150928941 34530294139015417556598353)
    ·
      refine ⟨25897720604261563167448765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34530294139015417556598353 25897720604261563167448765)
      ·
        refine ⟨9711645226598086187793287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25897720604261563167448765 9711645226598086187793287)
        ·
          refine ⟨14567467839897129281689931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9711645226598086187793287 14567467839897129281689931)
          ·
            refine ⟨21851201759845693922534897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14567467839897129281689931 21851201759845693922534897)
            ·
              refine ⟨16388401319884270441901173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21851201759845693922534897 16388401319884270441901173)
              ·
                refine ⟨1536412623739150353928235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16388401319884270441901173 1536412623739150353928235)
                ·
                  refine ⟨2304618935608725530892353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1536412623739150353928235 2304618935608725530892353)
                  ·
                    refine ⟨1728464201706544148169265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2304618935608725530892353 1728464201706544148169265)
                    ·
                      refine ⟨1296348151279908111126949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1728464201706544148169265 1296348151279908111126949)
                      ·
                        rfl

theorem cell23_2524629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_2524629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2524629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2524629 prefixEnd_2524629 := by exact prefixLift 2524629
  have htrace : WordTrace (prefixWord ++ tailWord_2524629) baseStart_2524629 baseEnd_2524629 := by
    simpa [prefixWord, tailWord_2524629, baseEnd_2524629] using wordTrace_append hprefix tailTrace_2524629
  have hstable : (prefixWord ++ tailWord_2524629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524629).length < 2 ^ (prefixWord ++ tailWord_2524629).sum := by decide
  have hdescent : baseEnd_2524629 < baseStart_2524629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524631 : List Nat := [1, 1, 3, 2, 1, 1, 1, 2, 4, 7]
def baseStart_2524631 : Nat := 118140960795 + 2524631 * 2 ^ 59
def prefixEnd_2524631 : Nat := 4983230072969 + 3 ^ 40 * 2524631 * 2
def baseEnd_2524631 : Nat := 432116392747072367767313

theorem tailTrace_2524631 : CollatzResearch.WordTrace tailWord_2524631 prefixEnd_2524631 432116392747072367767313 := by
  unfold tailWord_2524631
  simp only [CollatzResearch.WordTrace]
  refine ⟨92080857316700534492501747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61387238211133689661667831 92080857316700534492501747)
  ·
    refine ⟨138121285975050801738752621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92080857316700534492501747 138121285975050801738752621)
    ·
      refine ⟨51795482240644050652032233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138121285975050801738752621 51795482240644050652032233)
      ·
        refine ⟨38846611680483037989024175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51795482240644050652032233 38846611680483037989024175)
        ·
          refine ⟨58269917520724556983536263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38846611680483037989024175 58269917520724556983536263)
          ·
            refine ⟨87404876281086835475304395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58269917520724556983536263 87404876281086835475304395)
            ·
              refine ⟨131107314421630253212956593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87404876281086835475304395 131107314421630253212956593)
              ·
                refine ⟨98330485816222689909717445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131107314421630253212956593 98330485816222689909717445)
                ·
                  refine ⟨18436966090541754358072021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 98330485816222689909717445 18436966090541754358072021)
                  ·
                    refine ⟨432116392747072367767313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18436966090541754358072021 432116392747072367767313)
                    ·
                      rfl

theorem cell23_2524631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 7].length) (baseStart_2524631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2524631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2524631 prefixEnd_2524631 := by exact prefixLift 2524631
  have htrace : WordTrace (prefixWord ++ tailWord_2524631) baseStart_2524631 baseEnd_2524631 := by
    simpa [prefixWord, tailWord_2524631, baseEnd_2524631] using wordTrace_append hprefix tailTrace_2524631
  have hstable : (prefixWord ++ tailWord_2524631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524631).length < 2 ^ (prefixWord ++ tailWord_2524631).sum := by decide
  have hdescent : baseEnd_2524631 < baseStart_2524631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524655 : List Nat := [1, 1, 2, 1, 4, 1, 3, 2, 3, 3, 2]
def baseStart_2524655 : Nat := 118140960795 + 2524655 * 2 ^ 59
def prefixEnd_2524655 : Nat := 4983230072969 + 3 ^ 40 * 2524655 * 2
def baseEnd_2524655 : Nat := 1296361501776925009401829

theorem tailTrace_2524655 : CollatzResearch.WordTrace tailWord_2524655 prefixEnd_2524655 1296361501776925009401829 := by
  unfold tailWord_2524655
  simp only [CollatzResearch.WordTrace]
  refine ⟨92081732668613586591375419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61387821779075724394250279 92081732668613586591375419)
  ·
    refine ⟨138122599002920379887063129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92081732668613586591375419 138122599002920379887063129)
    ·
      refine ⟨103591949252190284915297347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138122599002920379887063129 103591949252190284915297347)
      ·
        refine ⟨155387923878285427372946021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103591949252190284915297347 155387923878285427372946021)
        ·
          refine ⟨29135235727178517632427379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 155387923878285427372946021 29135235727178517632427379)
          ·
            refine ⟨43702853590767776448641069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29135235727178517632427379 43702853590767776448641069)
            ·
              refine ⟨16388570096537916168240401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43702853590767776448641069 16388570096537916168240401)
              ·
                refine ⟨12291427572403437126180301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16388570096537916168240401 12291427572403437126180301)
                ·
                  refine ⟨4609285339651288922317613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12291427572403437126180301 4609285339651288922317613)
                  ·
                    refine ⟨1728482002369233345869105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4609285339651288922317613 1728482002369233345869105)
                    ·
                      refine ⟨1296361501776925009401829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1728482002369233345869105 1296361501776925009401829)
                      ·
                        rfl

theorem cell23_2524655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 3, 3, 2].length) (baseStart_2524655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2524655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2524655 prefixEnd_2524655 := by exact prefixLift 2524655
  have htrace : WordTrace (prefixWord ++ tailWord_2524655) baseStart_2524655 baseEnd_2524655 := by
    simpa [prefixWord, tailWord_2524655, baseEnd_2524655] using wordTrace_append hprefix tailTrace_2524655
  have hstable : (prefixWord ++ tailWord_2524655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524655).length < 2 ^ (prefixWord ++ tailWord_2524655).sum := by decide
  have hdescent : baseEnd_2524655 < baseStart_2524655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524662 : List Nat := [5, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3]
def baseStart_2524662 : Nat := 118140960795 + 2524662 * 2 ^ 59
def prefixEnd_2524662 : Nat := 4983230072969 + 3 ^ 40 * 2524662 * 2
def baseEnd_2524662 : Nat := 1296365096141506482014297

theorem tailTrace_2524662 : CollatzResearch.WordTrace tailWord_2524662 prefixEnd_2524662 1296365096141506482014297 := by
  unfold tailWord_2524662
  simp only [CollatzResearch.WordTrace]
  refine ⟨5755124248724264174180015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61387991986392151191253493 5755124248724264174180015)
  ·
    refine ⟨8632686373086396261270023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5755124248724264174180015 8632686373086396261270023)
    ·
      refine ⟨12949029559629594391905035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8632686373086396261270023 12949029559629594391905035)
      ·
        refine ⟨19423544339444391587857553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12949029559629594391905035 19423544339444391587857553)
        ·
          refine ⟨14567658254583293690893165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19423544339444391587857553 14567658254583293690893165)
          ·
            refine ⟨5462871845468735134084937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14567658254583293690893165 5462871845468735134084937)
            ·
              refine ⟨4097153884101551350563703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5462871845468735134084937 4097153884101551350563703)
              ·
                refine ⟨6145730826152327025845555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4097153884101551350563703 6145730826152327025845555)
                ·
                  refine ⟨9218596239228490538768333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6145730826152327025845555 9218596239228490538768333)
                  ·
                    refine ⟨3456973589710683952038125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9218596239228490538768333 3456973589710683952038125)
                    ·
                      refine ⟨1296365096141506482014297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3456973589710683952038125 1296365096141506482014297)
                      ·
                        rfl

theorem cell23_2524662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_2524662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2524662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2524662 prefixEnd_2524662 := by exact prefixLift 2524662
  have htrace : WordTrace (prefixWord ++ tailWord_2524662) baseStart_2524662 baseEnd_2524662 := by
    simpa [prefixWord, tailWord_2524662, baseEnd_2524662] using wordTrace_append hprefix tailTrace_2524662
  have hstable : (prefixWord ++ tailWord_2524662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524662).length < 2 ^ (prefixWord ++ tailWord_2524662).sum := by decide
  have hdescent : baseEnd_2524662 < baseStart_2524662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524696 : List Nat := [2, 1, 2, 3, 5, 1, 1, 2, 2, 1, 3]
def baseStart_2524696 : Nat := 118140960795 + 2524696 * 2 ^ 59
def prefixEnd_2524696 : Nat := 4983230072969 + 3 ^ 40 * 2524696 * 2
def baseEnd_2524696 : Nat := 1296382554483759348989141

theorem tailTrace_2524696 : CollatzResearch.WordTrace tailWord_2524696 prefixEnd_2524696 1296382554483759348989141 := by
  unfold tailWord_2524696
  simp only [CollatzResearch.WordTrace]
  refine ⟨46041614030732525296808971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61388818707643367062411961 46041614030732525296808971)
  ·
    refine ⟨69062421046098787945213457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46041614030732525296808971 69062421046098787945213457)
    ·
      refine ⟨51796815784574090958910093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69062421046098787945213457 51796815784574090958910093)
      ·
        refine ⟨19423805919215284109591285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51796815784574090958910093 19423805919215284109591285)
        ·
          refine ⟨1820981804926432885274183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19423805919215284109591285 1820981804926432885274183)
          ·
            refine ⟨2731472707389649327911275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1820981804926432885274183 2731472707389649327911275)
            ·
              refine ⟨4097209061084473991866913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2731472707389649327911275 4097209061084473991866913)
              ·
                refine ⟨3072906795813355493900185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4097209061084473991866913 3072906795813355493900185)
                ·
                  refine ⟨2304680096860016620425139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3072906795813355493900185 2304680096860016620425139)
                  ·
                    refine ⟨3457020145290024930637709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2304680096860016620425139 3457020145290024930637709)
                    ·
                      refine ⟨1296382554483759348989141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3457020145290024930637709 1296382554483759348989141)
                      ·
                        rfl

theorem cell23_2524696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 2, 2, 1, 3].length) (baseStart_2524696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2524696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2524696 prefixEnd_2524696 := by exact prefixLift 2524696
  have htrace : WordTrace (prefixWord ++ tailWord_2524696) baseStart_2524696 baseEnd_2524696 := by
    simpa [prefixWord, tailWord_2524696, baseEnd_2524696] using wordTrace_append hprefix tailTrace_2524696
  have hstable : (prefixWord ++ tailWord_2524696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524696).length < 2 ^ (prefixWord ++ tailWord_2524696).sum := by decide
  have hdescent : baseEnd_2524696 < baseStart_2524696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524785 : List Nat := [1, 2, 2, 2, 1, 1, 1, 6, 3, 4]
def baseStart_2524785 : Nat := 118140960795 + 2524785 * 2 ^ 59
def prefixEnd_2524785 : Nat := 4983230072969 + 3 ^ 40 * 2524785 * 2
def baseEnd_2524785 : Nat := 432142751420669833592077

theorem tailTrace_2524785 : CollatzResearch.WordTrace tailWord_2524785 prefixEnd_2524785 432142751420669833592077 := by
  unfold tailWord_2524785
  simp only [CollatzResearch.WordTrace]
  refine ⟨92086474158142618793607809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61390982772095079195738539 92086474158142618793607809)
  ·
    refine ⟨69064855618606964095205857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92086474158142618793607809 69064855618606964095205857)
    ·
      refine ⟨51798641713955223071404393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69064855618606964095205857 51798641713955223071404393)
      ·
        refine ⟨38848981285466417303553295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51798641713955223071404393 38848981285466417303553295)
        ·
          refine ⟨58273471928199625955329943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38848981285466417303553295 58273471928199625955329943)
          ·
            refine ⟨87410207892299438932994915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58273471928199625955329943 87410207892299438932994915)
            ·
              refine ⟨131115311838449158399492373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87410207892299438932994915 131115311838449158399492373)
              ·
                refine ⟨6146030242427304299976205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 131115311838449158399492373 6146030242427304299976205)
                ·
                  refine ⟨2304761340910239112491077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6146030242427304299976205 2304761340910239112491077)
                  ·
                    refine ⟨432142751420669833592077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2304761340910239112491077 432142751420669833592077)
                    ·
                      rfl

theorem cell23_2524785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6, 3, 4].length) (baseStart_2524785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2524785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2524785 prefixEnd_2524785 := by exact prefixLift 2524785
  have htrace : WordTrace (prefixWord ++ tailWord_2524785) baseStart_2524785 baseEnd_2524785 := by
    simpa [prefixWord, tailWord_2524785, baseEnd_2524785] using wordTrace_append hprefix tailTrace_2524785
  have hstable : (prefixWord ++ tailWord_2524785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524785).length < 2 ^ (prefixWord ++ tailWord_2524785).sum := by decide
  have hdescent : baseEnd_2524785 < baseStart_2524785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524866 : List Nat := [3, 5, 1, 2, 1, 1, 1, 1, 8]
def baseStart_2524866 : Nat := 118140960795 + 2524866 * 2 ^ 59
def prefixEnd_2524866 : Nat := 4983230072969 + 3 ^ 40 * 2524866 * 2
def baseEnd_2524866 : Nat := 144052205132780409318151

theorem tailTrace_2524866 : CollatzResearch.WordTrace tailWord_2524866 prefixEnd_2524866 144052205132780409318151 := by
  unfold tailWord_2524866
  simp only [CollatzResearch.WordTrace]
  refine ⟨23022357117712292406826613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61392952313899446418204301 23022357117712292406826613)
  ·
    refine ⟨2158345979785527413139995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23022357117712292406826613 2158345979785527413139995)
    ·
      refine ⟨3237518969678291119709993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2158345979785527413139995 3237518969678291119709993)
      ·
        refine ⟨2428139227258718339782495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3237518969678291119709993 2428139227258718339782495)
        ·
          refine ⟨3642208840888077509673743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2428139227258718339782495 3642208840888077509673743)
          ·
            refine ⟨5463313261332116264510615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3642208840888077509673743 5463313261332116264510615)
            ·
              refine ⟨8194969891998174396765923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5463313261332116264510615 8194969891998174396765923)
              ·
                refine ⟨12292454837997261595148885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8194969891998174396765923 12292454837997261595148885)
                ·
                  refine ⟨144052205132780409318151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12292454837997261595148885 144052205132780409318151)
                  ·
                    rfl

theorem cell23_2524866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_2524866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2524866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2524866 prefixEnd_2524866 := by exact prefixLift 2524866
  have htrace : WordTrace (prefixWord ++ tailWord_2524866) baseStart_2524866 baseEnd_2524866 := by
    simpa [prefixWord, tailWord_2524866, baseEnd_2524866] using wordTrace_append hprefix tailTrace_2524866
  have hstable : (prefixWord ++ tailWord_2524866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524866).length < 2 ^ (prefixWord ++ tailWord_2524866).sum := by decide
  have hdescent : baseEnd_2524866 < baseStart_2524866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524876 : List Nat := [2, 2, 1, 5, 2, 1, 2, 1, 3, 1, 3]
def baseStart_2524876 : Nat := 118140960795 + 2524876 * 2 ^ 59
def prefixEnd_2524876 : Nat := 4983230072969 + 3 ^ 40 * 2524876 * 2
def baseEnd_2524876 : Nat := 1296474981001568644738313

theorem tailTrace_2524876 : CollatzResearch.WordTrace tailWord_2524876 prefixEnd_2524876 1296474981001568644738313 := by
  unfold tailWord_2524876
  simp only [CollatzResearch.WordTrace]
  refine ⟨46044896600406470667585241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61393195467208627556780321 46044896600406470667585241)
  ·
    refine ⟨34533672450304853000688931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46044896600406470667585241 34533672450304853000688931)
    ·
      refine ⟨51800508675457279501033397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34533672450304853000688931 51800508675457279501033397)
      ·
        refine ⟨4856297688324119953221881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51800508675457279501033397 4856297688324119953221881)
        ·
          refine ⟨3642223266243089964916411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4856297688324119953221881 3642223266243089964916411)
          ·
            refine ⟨5463334899364634947374617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3642223266243089964916411 5463334899364634947374617)
            ·
              refine ⟨4097501174523476210530963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5463334899364634947374617 4097501174523476210530963)
              ·
                refine ⟨6146251761785214315796445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4097501174523476210530963 6146251761785214315796445)
                ·
                  refine ⟨2304844410669455368423667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6146251761785214315796445 2304844410669455368423667)
                  ·
                    refine ⟨3457266616004183052635501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2304844410669455368423667 3457266616004183052635501)
                    ·
                      refine ⟨1296474981001568644738313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3457266616004183052635501 1296474981001568644738313)
                      ·
                        rfl

theorem cell23_2524876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_2524876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2524876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2524876 prefixEnd_2524876 := by exact prefixLift 2524876
  have htrace : WordTrace (prefixWord ++ tailWord_2524876) baseStart_2524876 baseEnd_2524876 := by
    simpa [prefixWord, tailWord_2524876, baseEnd_2524876] using wordTrace_append hprefix tailTrace_2524876
  have hstable : (prefixWord ++ tailWord_2524876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524876).length < 2 ^ (prefixWord ++ tailWord_2524876).sum := by decide
  have hdescent : baseEnd_2524876 < baseStart_2524876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524895 : List Nat := [1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 6]
def baseStart_2524895 : Nat := 118140960795 + 2524895 * 2 ^ 59
def prefixEnd_2524895 : Nat := 4983230072969 + 3 ^ 40 * 2524895 * 2
def baseEnd_2524895 : Nat := 1296484737134004070400725

theorem tailTrace_2524895 : CollatzResearch.WordTrace tailWord_2524895 prefixEnd_2524895 1296484737134004070400725 := by
  unfold tailWord_2524895
  simp only [CollatzResearch.WordTrace]
  refine ⟨92090486187744107580112139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61393657458496071720074759 92090486187744107580112139)
  ·
    refine ⟨138135729281616161370168209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92090486187744107580112139 138135729281616161370168209)
    ·
      refine ⟨103601796961212121027626157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138135729281616161370168209 103601796961212121027626157)
      ·
        refine ⟨38850673860454545385359809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103601796961212121027626157 38850673860454545385359809)
        ·
          refine ⟨29138005395340909039019857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38850673860454545385359809 29138005395340909039019857)
          ·
            refine ⟨21853504046505681779264893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29138005395340909039019857 21853504046505681779264893)
            ·
              refine ⟨8195064017439630667224335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21853504046505681779264893 8195064017439630667224335)
              ·
                refine ⟨12292596026159446000836503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8195064017439630667224335 12292596026159446000836503)
                ·
                  refine ⟨18438894039239169001254755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12292596026159446000836503 18438894039239169001254755)
                  ·
                    refine ⟨27658341058858753501882133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18438894039239169001254755 27658341058858753501882133)
                    ·
                      refine ⟨1296484737134004070400725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27658341058858753501882133 1296484737134004070400725)
                      ·
                        rfl

theorem cell23_2524895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_2524895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2524895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2524895 prefixEnd_2524895 := by exact prefixLift 2524895
  have htrace : WordTrace (prefixWord ++ tailWord_2524895) baseStart_2524895 baseEnd_2524895 := by
    simpa [prefixWord, tailWord_2524895, baseEnd_2524895] using wordTrace_append hprefix tailTrace_2524895
  have hstable : (prefixWord ++ tailWord_2524895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524895).length < 2 ^ (prefixWord ++ tailWord_2524895).sum := by decide
  have hdescent : baseEnd_2524895 < baseStart_2524895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524934 : List Nat := [6, 2, 2, 1, 2, 1, 2, 1, 6]
def baseStart_2524934 : Nat := 118140960795 + 2524934 * 2 ^ 59
def prefixEnd_2524934 : Nat := 4983230072969 + 3 ^ 40 * 2524934 * 2
def baseEnd_2524934 : Nat := 144056084764392157534783

theorem tailTrace_2524934 : CollatzResearch.WordTrace tailWord_2524934 prefixEnd_2524934 144056084764392157534783 := by
  unfold tailWord_2524934
  simp only [CollatzResearch.WordTrace]
  refine ⟨2877872144831338038774433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 61394605756401878160521237 2877872144831338038774433)
  ·
    refine ⟨2158404108623503529080825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2877872144831338038774433 2158404108623503529080825)
    ·
      refine ⟨1618803081467627646810619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2158404108623503529080825 1618803081467627646810619)
      ·
        refine ⟨2428204622201441470215929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1618803081467627646810619 2428204622201441470215929)
        ·
          refine ⟨1821153466651081102661947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2428204622201441470215929 1821153466651081102661947)
          ·
            refine ⟨2731730199976621653992921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1821153466651081102661947 2731730199976621653992921)
            ·
              refine ⟨2048797649982466240494691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2731730199976621653992921 2048797649982466240494691)
              ·
                refine ⟨3073196474973699360742037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2048797649982466240494691 3073196474973699360742037)
                ·
                  refine ⟨144056084764392157534783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3073196474973699360742037 144056084764392157534783)
                  ·
                    rfl

theorem cell23_2524934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_2524934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2524934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2524934 prefixEnd_2524934 := by exact prefixLift 2524934
  have htrace : WordTrace (prefixWord ++ tailWord_2524934) baseStart_2524934 baseEnd_2524934 := by
    simpa [prefixWord, tailWord_2524934, baseEnd_2524934] using wordTrace_append hprefix tailTrace_2524934
  have hstable : (prefixWord ++ tailWord_2524934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524934).length < 2 ^ (prefixWord ++ tailWord_2524934).sum := by decide
  have hdescent : baseEnd_2524934 < baseStart_2524934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524955 : List Nat := [1, 1, 1, 1, 1, 1, 4, 4, 2, 3, 4]
def baseStart_2524955 : Nat := 118140960795 + 2524955 * 2 ^ 59
def prefixEnd_2524955 : Nat := 4983230072969 + 3 ^ 40 * 2524955 * 2
def baseEnd_2524955 : Nat := 1296515545973273835650449

theorem tailTrace_2524955 : CollatzResearch.WordTrace tailWord_2524955 prefixEnd_2524955 1296515545973273835650449 := by
  unfold tailWord_2524955
  simp only [CollatzResearch.WordTrace]
  refine ⟨92092674567526737827296319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61395116378351158551530879 92092674567526737827296319)
  ·
    refine ⟨138139011851290106740944479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92092674567526737827296319 138139011851290106740944479)
    ·
      refine ⟨207208517776935160111416719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138139011851290106740944479 207208517776935160111416719)
      ·
        refine ⟨310812776665402740167125079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207208517776935160111416719 310812776665402740167125079)
        ·
          refine ⟨466219164998104110250687619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310812776665402740167125079 466219164998104110250687619)
          ·
            refine ⟨699328747497156165376031429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 466219164998104110250687619 699328747497156165376031429)
            ·
              refine ⟨131124140155716781008005893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 699328747497156165376031429 131124140155716781008005893)
              ·
                refine ⟨24585776279196896439001105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 131124140155716781008005893 24585776279196896439001105)
                ·
                  refine ⟨18439332209397672329250829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24585776279196896439001105 18439332209397672329250829)
                  ·
                    refine ⟨6914749578524127123469061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18439332209397672329250829 6914749578524127123469061)
                    ·
                      refine ⟨1296515545973273835650449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6914749578524127123469061 1296515545973273835650449)
                      ·
                        rfl

theorem cell23_2524955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 3, 4].length) (baseStart_2524955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2524955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2524955 prefixEnd_2524955 := by exact prefixLift 2524955
  have htrace : WordTrace (prefixWord ++ tailWord_2524955) baseStart_2524955 baseEnd_2524955 := by
    simpa [prefixWord, tailWord_2524955, baseEnd_2524955] using wordTrace_append hprefix tailTrace_2524955
  have hstable : (prefixWord ++ tailWord_2524955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524955).length < 2 ^ (prefixWord ++ tailWord_2524955).sum := by decide
  have hdescent : baseEnd_2524955 < baseStart_2524955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524959 : List Nat := [1, 1, 2, 4, 2, 1, 3, 1, 3, 3, 2]
def baseStart_2524959 : Nat := 118140960795 + 2524959 * 2 ^ 59
def prefixEnd_2524959 : Nat := 4983230072969 + 3 ^ 40 * 2524959 * 2
def baseEnd_2524959 : Nat := 1296517599895891820000431

theorem tailTrace_2524959 : CollatzResearch.WordTrace tailWord_2524959 prefixEnd_2524959 1296517599895891820000431 := by
  unfold tailWord_2524959
  simp only [CollatzResearch.WordTrace]
  refine ⟨92092820459512246510441931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61395213639674831006961287 92092820459512246510441931)
  ·
    refine ⟨138139230689268369765662897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92092820459512246510441931 138139230689268369765662897)
    ·
      refine ⟨103604423016951277324247173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138139230689268369765662897 103604423016951277324247173)
      ·
        refine ⟨19425829315678364498296345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103604423016951277324247173 19425829315678364498296345)
        ·
          refine ⟨14569371986758773373722259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19425829315678364498296345 14569371986758773373722259)
          ·
            refine ⟨21854057980138160060583389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14569371986758773373722259 21854057980138160060583389)
            ·
              refine ⟨8195271742551810022718771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21854057980138160060583389 8195271742551810022718771)
              ·
                refine ⟨12292907613827715034078157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8195271742551810022718771 12292907613827715034078157)
                ·
                  refine ⟨4609840355185393137779309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12292907613827715034078157 4609840355185393137779309)
                  ·
                    refine ⟨1728690133194522426667241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4609840355185393137779309 1728690133194522426667241)
                    ·
                      refine ⟨1296517599895891820000431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1728690133194522426667241 1296517599895891820000431)
                      ·
                        rfl

theorem cell23_2524959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 3, 3, 2].length) (baseStart_2524959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2524959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2524959 prefixEnd_2524959 := by exact prefixLift 2524959
  have htrace : WordTrace (prefixWord ++ tailWord_2524959) baseStart_2524959 baseEnd_2524959 := by
    simpa [prefixWord, tailWord_2524959, baseEnd_2524959] using wordTrace_append hprefix tailTrace_2524959
  have hstable : (prefixWord ++ tailWord_2524959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524959).length < 2 ^ (prefixWord ++ tailWord_2524959).sum := by decide
  have hdescent : baseEnd_2524959 < baseStart_2524959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525002 : List Nat := [3, 1, 2, 1, 1, 1, 5, 1, 2, 2, 4]
def baseStart_2525002 : Nat := 118140960795 + 2525002 * 2 ^ 59
def prefixEnd_2525002 : Nat := 4983230072969 + 3 ^ 40 * 2525002 * 2
def baseEnd_2525002 : Nat := 1296539679564035151762733

theorem tailTrace_2525002 : CollatzResearch.WordTrace tailWord_2525002 prefixEnd_2525002 1296539679564035151762733 := by
  unfold tailWord_2525002
  simp only [CollatzResearch.WordTrace]
  refine ⟨23023597199589116213564315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61396259198904309902838173 23023597199589116213564315)
  ·
    refine ⟨34535395799383674320346473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23023597199589116213564315 34535395799383674320346473)
    ·
      refine ⟨25901546849537755740259855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34535395799383674320346473 25901546849537755740259855)
      ·
        refine ⟨38852320274306633610389783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25901546849537755740259855 38852320274306633610389783)
        ·
          refine ⟨58278480411459950415584675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38852320274306633610389783 58278480411459950415584675)
          ·
            refine ⟨87417720617189925623377013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58278480411459950415584675 87417720617189925623377013)
            ·
              refine ⟨8195411307861555527191595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 87417720617189925623377013 8195411307861555527191595)
              ·
                refine ⟨12293116961792333290787393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8195411307861555527191595 12293116961792333290787393)
                ·
                  refine ⟨9219837721344249968090545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12293116961792333290787393 9219837721344249968090545)
                  ·
                    refine ⟨6914878291008187476067909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9219837721344249968090545 6914878291008187476067909)
                    ·
                      refine ⟨1296539679564035151762733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6914878291008187476067909 1296539679564035151762733)
                      ·
                        rfl

theorem cell23_2525002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_2525002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2525002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2525002 prefixEnd_2525002 := by exact prefixLift 2525002
  have htrace : WordTrace (prefixWord ++ tailWord_2525002) baseStart_2525002 baseEnd_2525002 := by
    simpa [prefixWord, tailWord_2525002, baseEnd_2525002] using wordTrace_append hprefix tailTrace_2525002
  have hstable : (prefixWord ++ tailWord_2525002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525002).length < 2 ^ (prefixWord ++ tailWord_2525002).sum := by decide
  have hdescent : baseEnd_2525002 < baseStart_2525002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525012 : List Nat := [2, 4, 1, 1, 3, 1, 1, 1, 9]
def baseStart_2525012 : Nat := 118140960795 + 2525012 * 2 ^ 59
def prefixEnd_2525012 : Nat := 4983230072969 + 3 ^ 40 * 2525012 * 2
def baseEnd_2525012 : Nat := 144060534930064456959743

theorem tailTrace_2525012 : CollatzResearch.WordTrace tailWord_2525012 prefixEnd_2525012 144060534930064456959743 := by
  unfold tailWord_2525012
  simp only [CollatzResearch.WordTrace]
  refine ⟨46047376764160118281060645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61396502352213491041414193 46047376764160118281060645)
  ·
    refine ⟨8633883143280022177698871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46047376764160118281060645 8633883143280022177698871)
    ·
      refine ⟨12950824714920033266548307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8633883143280022177698871 12950824714920033266548307)
      ·
        refine ⟨19426237072380049899822461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12950824714920033266548307 19426237072380049899822461)
        ·
          refine ⟨7284838902142518712433423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19426237072380049899822461 7284838902142518712433423)
          ·
            refine ⟨10927258353213778068650135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7284838902142518712433423 10927258353213778068650135)
            ·
              refine ⟨16390887529820667102975203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10927258353213778068650135 16390887529820667102975203)
              ·
                refine ⟨24586331294731000654462805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16390887529820667102975203 24586331294731000654462805)
                ·
                  refine ⟨144060534930064456959743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 24586331294731000654462805 144060534930064456959743)
                  ·
                    rfl

theorem cell23_2525012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 9].length) (baseStart_2525012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2525012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2525012 prefixEnd_2525012 := by exact prefixLift 2525012
  have htrace : WordTrace (prefixWord ++ tailWord_2525012) baseStart_2525012 baseEnd_2525012 := by
    simpa [prefixWord, tailWord_2525012, baseEnd_2525012] using wordTrace_append hprefix tailTrace_2525012
  have hstable : (prefixWord ++ tailWord_2525012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525012).length < 2 ^ (prefixWord ++ tailWord_2525012).sum := by decide
  have hdescent : baseEnd_2525012 < baseStart_2525012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525042 : List Nat := [3, 2, 1, 2, 1, 1, 1, 3, 4, 5]
def baseStart_2525042 : Nat := 118140960795 + 2525042 * 2 ^ 59
def prefixEnd_2525042 : Nat := 4983230072969 + 3 ^ 40 * 2525042 * 2
def baseEnd_2525042 : Nat := 432186739596738331754183

theorem tailTrace_2525042 : CollatzResearch.WordTrace tailWord_2525042 prefixEnd_2525042 432186739596738331754183 := by
  unfold tailWord_2525042
  simp only [CollatzResearch.WordTrace]
  refine ⟨23023961929552887921428345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61397231812141034457142253 23023961929552887921428345)
  ·
    refine ⟨17267971447164665941071259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23023961929552887921428345 17267971447164665941071259)
    ·
      refine ⟨25901957170746998911606889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17267971447164665941071259 25901957170746998911606889)
      ·
        refine ⟨19426467878060249183705167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25901957170746998911606889 19426467878060249183705167)
        ·
          refine ⟨29139701817090373775557751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19426467878060249183705167 29139701817090373775557751)
          ·
            refine ⟨43709552725635560663336627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29139701817090373775557751 43709552725635560663336627)
            ·
              refine ⟨65564329088453340995004941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43709552725635560663336627 65564329088453340995004941)
              ·
                refine ⟨24586623408170002873126853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65564329088453340995004941 24586623408170002873126853)
                ·
                  refine ⟨4609991889031875538711285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24586623408170002873126853 4609991889031875538711285)
                  ·
                    refine ⟨432186739596738331754183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4609991889031875538711285 432186739596738331754183)
                    ·
                      rfl

theorem cell23_2525042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 4, 5].length) (baseStart_2525042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2525042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2525042 prefixEnd_2525042 := by exact prefixLift 2525042
  have htrace : WordTrace (prefixWord ++ tailWord_2525042) baseStart_2525042 baseEnd_2525042 := by
    simpa [prefixWord, tailWord_2525042, baseEnd_2525042] using wordTrace_append hprefix tailTrace_2525042
  have hstable : (prefixWord ++ tailWord_2525042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525042).length < 2 ^ (prefixWord ++ tailWord_2525042).sum := by decide
  have hdescent : baseEnd_2525042 < baseStart_2525042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525046 : List Nat := [5, 1, 1, 3, 2, 1, 2, 1, 7]
def baseStart_2525046 : Nat := 118140960795 + 2525046 * 2 ^ 59
def prefixEnd_2525046 : Nat := 4983230072969 + 3 ^ 40 * 2525046 * 2
def baseEnd_2525046 : Nat := 144062474745870331068059

theorem tailTrace_2525046 : CollatzResearch.WordTrace tailWord_2525046 prefixEnd_2525046 144062474745870331068059 := by
  unfold tailWord_2525046
  simp only [CollatzResearch.WordTrace]
  refine ⟨5755999600637316273053687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61397329073464706912572661 5755999600637316273053687)
  ·
    refine ⟨8633999400955974409580531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5755999600637316273053687 8633999400955974409580531)
    ·
      refine ⟨12950999101433961614370797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8633999400955974409580531 12950999101433961614370797)
      ·
        refine ⟨4856624663037735605389049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12950999101433961614370797 4856624663037735605389049)
        ·
          refine ⟨3642468497278301704041787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4856624663037735605389049 3642468497278301704041787)
          ·
            refine ⟨5463702745917452556062681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3642468497278301704041787 5463702745917452556062681)
            ·
              refine ⟨4097777059438089417047011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5463702745917452556062681 4097777059438089417047011)
              ·
                refine ⟨6146665589157134125570517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4097777059438089417047011 6146665589157134125570517)
                ·
                  refine ⟨144062474745870331068059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6146665589157134125570517 144062474745870331068059)
                  ·
                    rfl

theorem cell23_2525046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 1, 7].length) (baseStart_2525046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2525046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2525046 prefixEnd_2525046 := by exact prefixLift 2525046
  have htrace : WordTrace (prefixWord ++ tailWord_2525046) baseStart_2525046 baseEnd_2525046 := by
    simpa [prefixWord, tailWord_2525046, baseEnd_2525046] using wordTrace_append hprefix tailTrace_2525046
  have hstable : (prefixWord ++ tailWord_2525046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525046).length < 2 ^ (prefixWord ++ tailWord_2525046).sum := by decide
  have hdescent : baseEnd_2525046 < baseStart_2525046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525057 : List Nat := [1, 2, 4, 4, 1, 1, 3, 1, 2, 2, 2]
def baseStart_2525057 : Nat := 118140960795 + 2525057 * 2 ^ 59
def prefixEnd_2525057 : Nat := 4983230072969 + 3 ^ 40 * 2525057 * 2
def baseEnd_2525057 : Nat := 1296567921000032436574981

theorem tailTrace_2525057 : CollatzResearch.WordTrace tailWord_2525057 prefixEnd_2525057 1296567921000032436574981 := by
  unfold tailWord_2525057
  simp only [CollatzResearch.WordTrace]
  refine ⟨92096394813157209247509425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61397596542104806165006283 92096394813157209247509425)
  ·
    refine ⟨69072296109867906935632069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92096394813157209247509425 69072296109867906935632069)
    ·
      refine ⟨12951055520600232550431013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69072296109867906935632069 12951055520600232550431013)
      ·
        refine ⟨2428322910112543603205815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12951055520600232550431013 2428322910112543603205815)
        ·
          refine ⟨3642484365168815404808723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2428322910112543603205815 3642484365168815404808723)
          ·
            refine ⟨5463726547753223107213085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3642484365168815404808723 5463726547753223107213085)
            ·
              refine ⟨2048897455407458665204907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5463726547753223107213085 2048897455407458665204907)
              ·
                refine ⟨3073346183111187997807361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2048897455407458665204907 3073346183111187997807361)
                ·
                  refine ⟨2305009637333390998355521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3073346183111187997807361 2305009637333390998355521)
                  ·
                    refine ⟨1728757228000043248766641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2305009637333390998355521 1728757228000043248766641)
                    ·
                      refine ⟨1296567921000032436574981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1728757228000043248766641 1296567921000032436574981)
                      ·
                        rfl

theorem cell23_2525057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_2525057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2525057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2525057 prefixEnd_2525057 := by exact prefixLift 2525057
  have htrace : WordTrace (prefixWord ++ tailWord_2525057) baseStart_2525057 baseEnd_2525057 := by
    simpa [prefixWord, tailWord_2525057, baseEnd_2525057] using wordTrace_append hprefix tailTrace_2525057
  have hstable : (prefixWord ++ tailWord_2525057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525057).length < 2 ^ (prefixWord ++ tailWord_2525057).sum := by decide
  have hdescent : baseEnd_2525057 < baseStart_2525057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525080 : List Nat := [2, 1, 2, 6, 2, 1, 1, 3, 5]
def baseStart_2525080 : Nat := 118140960795 + 2525080 * 2 ^ 59
def prefixEnd_2525080 : Nat := 4983230072969 + 3 ^ 40 * 2525080 * 2
def baseEnd_2525080 : Nat := 144064414561676205176375

theorem tailTrace_2525080 : CollatzResearch.WordTrace tailWord_2525080 prefixEnd_2525080 144064414561676205176375 := by
  unfold tailWord_2525080
  simp only [CollatzResearch.WordTrace]
  refine ⟨46048616846036942087798347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61398155794715922783731129 46048616846036942087798347)
  ·
    refine ⟨69072925269055413131697521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46048616846036942087798347 69072925269055413131697521)
    ·
      refine ⟨51804693951791559848773141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69072925269055413131697521 51804693951791559848773141)
      ·
        refine ⟨2428345028990229367911241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 51804693951791559848773141 2428345028990229367911241)
        ·
          refine ⟨1821258771742672025933431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2428345028990229367911241 1821258771742672025933431)
          ·
            refine ⟨2731888157614008038900147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1821258771742672025933431 2731888157614008038900147)
            ·
              refine ⟨4097832236421012058350221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2731888157614008038900147 4097832236421012058350221)
              ·
                refine ⟨1536687088657879521881333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4097832236421012058350221 1536687088657879521881333)
                ·
                  refine ⟨144064414561676205176375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1536687088657879521881333 144064414561676205176375)
                  ·
                    rfl

theorem cell23_2525080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 3, 5].length) (baseStart_2525080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2525080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2525080 prefixEnd_2525080 := by exact prefixLift 2525080
  have htrace : WordTrace (prefixWord ++ tailWord_2525080) baseStart_2525080 baseEnd_2525080 := by
    simpa [prefixWord, tailWord_2525080, baseEnd_2525080] using wordTrace_append hprefix tailTrace_2525080
  have hstable : (prefixWord ++ tailWord_2525080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525080).length < 2 ^ (prefixWord ++ tailWord_2525080).sum := by decide
  have hdescent : baseEnd_2525080 < baseStart_2525080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525106 : List Nat := [3, 2, 1, 1, 1, 1, 1, 8, 1, 4]
def baseStart_2525106 : Nat := 118140960795 + 2525106 * 2 ^ 59
def prefixEnd_2525106 : Nat := 4983230072969 + 3 ^ 40 * 2525106 * 2
def baseEnd_2525106 : Nat := 432197693850700914954085

theorem tailTrace_2525106 : CollatzResearch.WordTrace tailWord_2525106 prefixEnd_2525106 432197693850700914954085 := by
  unfold tailWord_2525106
  simp only [CollatzResearch.WordTrace]
  refine ⟨23024545497494922654010793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61398787993319793744028781 23024545497494922654010793)
  ·
    refine ⟨17268409123121191990508095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23024545497494922654010793 17268409123121191990508095)
    ·
      refine ⟨25902613684681787985762143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17268409123121191990508095 25902613684681787985762143)
      ·
        refine ⟨38853920527022681978643215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25902613684681787985762143 38853920527022681978643215)
        ·
          refine ⟨58280880790534022967964823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38853920527022681978643215 58280880790534022967964823)
          ·
            refine ⟨87421321185801034451947235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58280880790534022967964823 87421321185801034451947235)
            ·
              refine ⟨131131981778701551677920853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87421321185801034451947235 131131981778701551677920853)
              ·
                refine ⟨1536702911469158808725635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 131131981778701551677920853 1536702911469158808725635)
                ·
                  refine ⟨2305054367203738213088453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1536702911469158808725635 2305054367203738213088453)
                  ·
                    refine ⟨432197693850700914954085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2305054367203738213088453 432197693850700914954085)
                    ·
                      rfl

theorem cell23_2525106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 8, 1, 4].length) (baseStart_2525106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2525106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2525106 prefixEnd_2525106 := by exact prefixLift 2525106
  have htrace : WordTrace (prefixWord ++ tailWord_2525106) baseStart_2525106 baseEnd_2525106 := by
    simpa [prefixWord, tailWord_2525106, baseEnd_2525106] using wordTrace_append hprefix tailTrace_2525106
  have hstable : (prefixWord ++ tailWord_2525106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525106).length < 2 ^ (prefixWord ++ tailWord_2525106).sum := by decide
  have hdescent : baseEnd_2525106 < baseStart_2525106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525156 : List Nat := [2, 3, 1, 1, 1, 1, 3, 4, 2, 3, 2]
def baseStart_2525156 : Nat := 118140960795 + 2525156 * 2 ^ 59
def prefixEnd_2525156 : Nat := 4983230072969 + 3 ^ 40 * 2525156 * 2
def baseEnd_2525156 : Nat := 1296618755584827549237025

theorem tailTrace_2525156 : CollatzResearch.WordTrace tailWord_2525156 prefixEnd_2525156 1296618755584827549237025 := by
  unfold tailWord_2525156
  simp only [CollatzResearch.WordTrace]
  refine ⟨46050002819899274577681661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61400003759865699436908881 46050002819899274577681661)
  ·
    refine ⟨17268751057462227966630623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46050002819899274577681661 17268751057462227966630623)
    ·
      refine ⟨25903126586193341949945935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17268751057462227966630623 25903126586193341949945935)
      ·
        refine ⟨38854689879290012924918903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25903126586193341949945935 38854689879290012924918903)
        ·
          refine ⟨58282034818935019387378355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38854689879290012924918903 58282034818935019387378355)
          ·
            refine ⟨87423052228402529081067533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58282034818935019387378355 87423052228402529081067533)
            ·
              refine ⟨32783644585650948405400325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87423052228402529081067533 32783644585650948405400325)
              ·
                refine ⟨6146933359809552826012561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32783644585650948405400325 6146933359809552826012561)
                ·
                  refine ⟨4610200019857164619509421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6146933359809552826012561 4610200019857164619509421)
                  ·
                    refine ⟨1728825007446436732316033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4610200019857164619509421 1728825007446436732316033)
                    ·
                      refine ⟨1296618755584827549237025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1728825007446436732316033 1296618755584827549237025)
                      ·
                        rfl

theorem cell23_2525156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4, 2, 3, 2].length) (baseStart_2525156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2525156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2525156 prefixEnd_2525156 := by exact prefixLift 2525156
  have htrace : WordTrace (prefixWord ++ tailWord_2525156) baseStart_2525156 baseEnd_2525156 := by
    simpa [prefixWord, tailWord_2525156, baseEnd_2525156] using wordTrace_append hprefix tailTrace_2525156
  have hstable : (prefixWord ++ tailWord_2525156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525156).length < 2 ^ (prefixWord ++ tailWord_2525156).sum := by decide
  have hdescent : baseEnd_2525156 < baseStart_2525156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525213 : List Nat := [1, 4, 2, 2, 2, 1, 3, 2, 2, 4]
def baseStart_2525213 : Nat := 118140960795 + 2525213 * 2 ^ 59
def prefixEnd_2525213 : Nat := 4983230072969 + 3 ^ 40 * 2525213 * 2
def baseEnd_2525213 : Nat := 432216007994044608741421

theorem tailTrace_2525213 : CollatzResearch.WordTrace tailWord_2525213 prefixEnd_2525213 432216007994044608741421 := by
  unfold tailWord_2525213
  simp only [CollatzResearch.WordTrace]
  refine ⟨92102084600592047890188293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61401389733728031926792195 92102084600592047890188293)
  ·
    refine ⟨17269140862611008979410305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92102084600592047890188293 17269140862611008979410305)
    ·
      refine ⟨12951855646958256734557729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17269140862611008979410305 12951855646958256734557729)
      ·
        refine ⟨9713891735218692550918297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12951855646958256734557729 9713891735218692550918297)
        ·
          refine ⟨7285418801414019413188723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9713891735218692550918297 7285418801414019413188723)
          ·
            refine ⟨10928128202121029119783085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7285418801414019413188723 10928128202121029119783085)
            ·
              refine ⟨4098048075795385919918657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10928128202121029119783085 4098048075795385919918657)
              ·
                refine ⟨3073536056846539439938993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4098048075795385919918657 3073536056846539439938993)
                ·
                  refine ⟨2305152042634904579954245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3073536056846539439938993 2305152042634904579954245)
                  ·
                    refine ⟨432216007994044608741421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2305152042634904579954245 432216007994044608741421)
                    ·
                      rfl

theorem cell23_2525213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_2525213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2525213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2525213 prefixEnd_2525213 := by exact prefixLift 2525213
  have htrace : WordTrace (prefixWord ++ tailWord_2525213) baseStart_2525213 baseEnd_2525213 := by
    simpa [prefixWord, tailWord_2525213, baseEnd_2525213] using wordTrace_append hprefix tailTrace_2525213
  have hstable : (prefixWord ++ tailWord_2525213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525213).length < 2 ^ (prefixWord ++ tailWord_2525213).sum := by decide
  have hdescent : baseEnd_2525213 < baseStart_2525213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525223 : List Nat := [1, 1, 7, 1, 2, 1, 1, 2, 1, 1, 5]
def baseStart_2525223 : Nat := 118140960795 + 2525223 * 2 ^ 59
def prefixEnd_2525223 : Nat := 4983230072969 + 3 ^ 40 * 2525223 * 2
def baseEnd_2525223 : Nat := 1296653158788678787099217

theorem tailTrace_2525223 : CollatzResearch.WordTrace tailWord_2525223 prefixEnd_2525223 1296653158788678787099217 := by
  unfold tailWord_2525223
  simp only [CollatzResearch.WordTrace]
  refine ⟨92102449330555819598052323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61401632887037213065368215 92102449330555819598052323)
  ·
    refine ⟨138153673995833729397078485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92102449330555819598052323 138153673995833729397078485)
    ·
      refine ⟨3237976734277353032744027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 138153673995833729397078485 3237976734277353032744027)
      ·
        refine ⟨4856965101416029549116041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3237976734277353032744027 4856965101416029549116041)
        ·
          refine ⟨3642723826062022161837031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4856965101416029549116041 3642723826062022161837031)
          ·
            refine ⟨5464085739093033242755547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3642723826062022161837031 5464085739093033242755547)
            ·
              refine ⟨8196128608639549864133321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5464085739093033242755547 8196128608639549864133321)
              ·
                refine ⟨6147096456479662398099991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8196128608639549864133321 6147096456479662398099991)
                ·
                  refine ⟨9220644684719493597149987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6147096456479662398099991 9220644684719493597149987)
                  ·
                    refine ⟨13830967027079240395724981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9220644684719493597149987 13830967027079240395724981)
                    ·
                      refine ⟨1296653158788678787099217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13830967027079240395724981 1296653158788678787099217)
                      ·
                        rfl

theorem cell23_2525223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_2525223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2525223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2525223 prefixEnd_2525223 := by exact prefixLift 2525223
  have htrace : WordTrace (prefixWord ++ tailWord_2525223) baseStart_2525223 baseEnd_2525223 := by
    simpa [prefixWord, tailWord_2525223, baseEnd_2525223] using wordTrace_append hprefix tailTrace_2525223
  have hstable : (prefixWord ++ tailWord_2525223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525223).length < 2 ^ (prefixWord ++ tailWord_2525223).sum := by decide
  have hdescent : baseEnd_2525223 < baseStart_2525223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525230 : List Nat := [4, 1, 3, 1, 1, 3, 3, 1, 2, 4]
def baseStart_2525230 : Nat := 118140960795 + 2525230 * 2 ^ 59
def prefixEnd_2525230 : Nat := 4983230072969 + 3 ^ 40 * 2525230 * 2
def baseEnd_2525230 : Nat := 432218917717753419903895

theorem tailTrace_2525230 : CollatzResearch.WordTrace tailWord_2525230 prefixEnd_2525230 432218917717753419903895 := by
  unfold tailWord_2525230
  simp only [CollatzResearch.WordTrace]
  refine ⟨11512838080191307474194643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61401803094353639862371429 11512838080191307474194643)
  ·
    refine ⟨17269257120286961211291965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11512838080191307474194643 17269257120286961211291965)
    ·
      refine ⟨6475971420107610454234487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17269257120286961211291965 6475971420107610454234487)
      ·
        refine ⟨9713957130161415681351731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6475971420107610454234487 9713957130161415681351731)
        ·
          refine ⟨14570935695242123522027597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9713957130161415681351731 14570935695242123522027597)
          ·
            refine ⟨5464100885715796320760349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14570935695242123522027597 5464100885715796320760349)
            ·
              refine ⟨2049037832143423620285131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5464100885715796320760349 2049037832143423620285131)
              ·
                refine ⟨3073556748215135430427697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2049037832143423620285131 3073556748215135430427697)
                ·
                  refine ⟨2305167561161351572820773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3073556748215135430427697 2305167561161351572820773)
                  ·
                    refine ⟨432218917717753419903895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2305167561161351572820773 432218917717753419903895)
                    ·
                      rfl

theorem cell23_2525230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_2525230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2525230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2525230 prefixEnd_2525230 := by exact prefixLift 2525230
  have htrace : WordTrace (prefixWord ++ tailWord_2525230) baseStart_2525230 baseEnd_2525230 := by
    simpa [prefixWord, tailWord_2525230, baseEnd_2525230] using wordTrace_append hprefix tailTrace_2525230
  have hstable : (prefixWord ++ tailWord_2525230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525230).length < 2 ^ (prefixWord ++ tailWord_2525230).sum := by decide
  have hdescent : baseEnd_2525230 < baseStart_2525230 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525289 : List Nat := [1, 2, 1, 1, 1, 5, 2, 1, 1, 4, 4]
def baseStart_2525289 : Nat := 118140960795 + 2525289 * 2 ^ 59
def prefixEnd_2525289 : Nat := 4983230072969 + 3 ^ 40 * 2525289 * 2
def baseEnd_2525289 : Nat := 1296687048511875528873913

theorem tailTrace_2525289 : CollatzResearch.WordTrace tailWord_2525289 prefixEnd_2525289 1296687048511875528873913 := by
  unfold tailWord_2525289
  simp only [CollatzResearch.WordTrace]
  refine ⟨92104856548316712869954921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61403237698877808579969947 92104856548316712869954921)
  ·
    refine ⟨69078642411237534652466191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92104856548316712869954921 69078642411237534652466191)
    ·
      refine ⟨103617963616856301978699287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69078642411237534652466191 103617963616856301978699287)
      ·
        refine ⟨155426945425284452968048931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103617963616856301978699287 155426945425284452968048931)
        ·
          refine ⟨233140418137926679452073397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155426945425284452968048931 233140418137926679452073397)
          ·
            refine ⟨21856914200430626198631881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 233140418137926679452073397 21856914200430626198631881)
            ·
              refine ⟨16392685650322969648973911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21856914200430626198631881 16392685650322969648973911)
              ·
                refine ⟨24589028475484454473460867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16392685650322969648973911 24589028475484454473460867)
                ·
                  refine ⟨36883542713226681710191301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24589028475484454473460867 36883542713226681710191301)
                  ·
                    refine ⟨6915664258730002820660869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36883542713226681710191301 6915664258730002820660869)
                    ·
                      refine ⟨1296687048511875528873913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6915664258730002820660869 1296687048511875528873913)
                      ·
                        rfl

theorem cell23_2525289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 4, 4].length) (baseStart_2525289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2525289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2525289 prefixEnd_2525289 := by exact prefixLift 2525289
  have htrace : WordTrace (prefixWord ++ tailWord_2525289) baseStart_2525289 baseEnd_2525289 := by
    simpa [prefixWord, tailWord_2525289, baseEnd_2525289] using wordTrace_append hprefix tailTrace_2525289
  have hstable : (prefixWord ++ tailWord_2525289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525289).length < 2 ^ (prefixWord ++ tailWord_2525289).sum := by decide
  have hdescent : baseEnd_2525289 < baseStart_2525289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525293 : List Nat := [1, 5, 1, 1, 2, 1, 2, 3, 1, 4, 2]
def baseStart_2525293 : Nat := 118140960795 + 2525293 * 2 ^ 59
def prefixEnd_2525293 : Nat := 4983230072969 + 3 ^ 40 * 2525293 * 2
def baseEnd_2525293 : Nat := 1296689102434493513223895

theorem tailTrace_2525293 : CollatzResearch.WordTrace tailWord_2525293 prefixEnd_2525293 1296689102434493513223895 := by
  unfold tailWord_2525293
  simp only [CollatzResearch.WordTrace]
  refine ⟨92105002440302221553100533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61403334960201481035400355 92105002440302221553100533)
  ·
    refine ⟨8634843978778333270603175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 92105002440302221553100533 8634843978778333270603175)
    ·
      refine ⟨12952265968167499905904763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8634843978778333270603175 12952265968167499905904763)
      ·
        refine ⟨19428398952251249858857145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12952265968167499905904763 19428398952251249858857145)
        ·
          refine ⟨14571299214188437394142859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19428398952251249858857145 14571299214188437394142859)
          ·
            refine ⟨21856948821282656091214289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14571299214188437394142859 21856948821282656091214289)
            ·
              refine ⟨16392711615961992068410717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21856948821282656091214289 16392711615961992068410717)
              ·
                refine ⟨6147266855985747025654019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16392711615961992068410717 6147266855985747025654019)
                ·
                  refine ⟨9220900283978620538481029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6147266855985747025654019 9220900283978620538481029)
                  ·
                    refine ⟨1728918803245991350965193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9220900283978620538481029 1728918803245991350965193)
                    ·
                      refine ⟨1296689102434493513223895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1728918803245991350965193 1296689102434493513223895)
                      ·
                        rfl

theorem cell23_2525293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 3, 1, 4, 2].length) (baseStart_2525293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2525293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2525293 prefixEnd_2525293 := by exact prefixLift 2525293
  have htrace : WordTrace (prefixWord ++ tailWord_2525293) baseStart_2525293 baseEnd_2525293 := by
    simpa [prefixWord, tailWord_2525293, baseEnd_2525293] using wordTrace_append hprefix tailTrace_2525293
  have hstable : (prefixWord ++ tailWord_2525293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525293).length < 2 ^ (prefixWord ++ tailWord_2525293).sum := by decide
  have hdescent : baseEnd_2525293 < baseStart_2525293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525339 : List Nat := [1, 1, 1, 1, 1, 1, 2, 7, 1, 2, 5]
def baseStart_2525339 : Nat := 118140960795 + 2525339 * 2 ^ 59
def prefixEnd_2525339 : Nat := 4983230072969 + 3 ^ 40 * 2525339 * 2
def baseEnd_2525339 : Nat := 1296712722544600333248683

theorem tailTrace_2525339 : CollatzResearch.WordTrace tailWord_2525339 prefixEnd_2525339 1296712722544600333248683 := by
  unfold tailWord_2525339
  simp only [CollatzResearch.WordTrace]
  refine ⟨92106680198135571409275071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61404453465423714272850047 92106680198135571409275071)
  ·
    refine ⟨138160020297203357113912607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92106680198135571409275071 138160020297203357113912607)
    ·
      refine ⟨207240030445805035670868911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138160020297203357113912607 207240030445805035670868911)
      ·
        refine ⟨310860045668707553506303367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207240030445805035670868911 310860045668707553506303367)
        ·
          refine ⟨466290068503061330259455051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310860045668707553506303367 466290068503061330259455051)
          ·
            refine ⟨699435102754591995389182577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 466290068503061330259455051 699435102754591995389182577)
            ·
              refine ⟨524576327065943996541886933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 699435102754591995389182577 524576327065943996541886933)
              ·
                refine ⟨12294757665608062418950475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 524576327065943996541886933 12294757665608062418950475)
                ·
                  refine ⟨18442136498412093628425713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12294757665608062418950475 18442136498412093628425713)
                  ·
                    refine ⟨13831602373809070221319285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18442136498412093628425713 13831602373809070221319285)
                    ·
                      refine ⟨1296712722544600333248683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13831602373809070221319285 1296712722544600333248683)
                      ·
                        rfl

theorem cell23_2525339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 2, 5].length) (baseStart_2525339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2525339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2525339 prefixEnd_2525339 := by exact prefixLift 2525339
  have htrace : WordTrace (prefixWord ++ tailWord_2525339) baseStart_2525339 baseEnd_2525339 := by
    simpa [prefixWord, tailWord_2525339, baseEnd_2525339] using wordTrace_append hprefix tailTrace_2525339
  have hstable : (prefixWord ++ tailWord_2525339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525339).length < 2 ^ (prefixWord ++ tailWord_2525339).sum := by decide
  have hdescent : baseEnd_2525339 < baseStart_2525339 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525343 : List Nat := [1, 1, 2, 6, 1, 2, 1, 1, 2, 3, 3]
def baseStart_2525343 : Nat := 118140960795 + 2525343 * 2 ^ 59
def prefixEnd_2525343 : Nat := 4983230072969 + 3 ^ 40 * 2525343 * 2
def baseEnd_2525343 : Nat := 1296714776467218317598665

theorem tailTrace_2525343 : CollatzResearch.WordTrace tailWord_2525343 prefixEnd_2525343 1296714776467218317598665 := by
  unfold tailWord_2525343
  simp only [CollatzResearch.WordTrace]
  refine ⟨92106826090121080092420683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61404550726747386728280455 92106826090121080092420683)
  ·
    refine ⟨138160239135181620138631025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92106826090121080092420683 138160239135181620138631025)
    ·
      refine ⟨103620179351386215103973269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138160239135181620138631025 103620179351386215103973269)
      ·
        refine ⟨4857195907096228832998747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 103620179351386215103973269 4857195907096228832998747)
        ·
          refine ⟨7285793860644343249498121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4857195907096228832998747 7285793860644343249498121)
          ·
            refine ⟨5464345395483257437123591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7285793860644343249498121 5464345395483257437123591)
            ·
              refine ⟨8196518093224886155685387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5464345395483257437123591 8196518093224886155685387)
              ·
                refine ⟨12294777139837329233528081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8196518093224886155685387 12294777139837329233528081)
                ·
                  refine ⟨9221082854877996925146061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12294777139837329233528081 9221082854877996925146061)
                  ·
                    refine ⟨3457906070579248846929773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9221082854877996925146061 3457906070579248846929773)
                    ·
                      refine ⟨1296714776467218317598665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3457906070579248846929773 1296714776467218317598665)
                      ·
                        rfl

theorem cell23_2525343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_2525343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2525343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2525343 prefixEnd_2525343 := by exact prefixLift 2525343
  have htrace : WordTrace (prefixWord ++ tailWord_2525343) baseStart_2525343 baseEnd_2525343 := by
    simpa [prefixWord, tailWord_2525343, baseEnd_2525343] using wordTrace_append hprefix tailTrace_2525343
  have hstable : (prefixWord ++ tailWord_2525343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525343).length < 2 ^ (prefixWord ++ tailWord_2525343).sum := by decide
  have hdescent : baseEnd_2525343 < baseStart_2525343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525444 : List Nat := [2, 3, 2, 2, 3, 1, 3, 2, 1, 4]
def baseStart_2525444 : Nat := 118140960795 + 2525444 * 2 ^ 59
def prefixEnd_2525444 : Nat := 4983230072969 + 3 ^ 40 * 2525444 * 2
def baseEnd_2525444 : Nat := 432255546004440807478567

theorem tailTrace_2525444 : CollatzResearch.WordTrace tailWord_2525444 prefixEnd_2525444 432255546004440807478567 := by
  unfold tailWord_2525444
  simp only [CollatzResearch.WordTrace]
  refine ⟨46055254931377587170923693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61407006575170116227898257 46055254931377587170923693)
  ·
    refine ⟨17270720599266595189096385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46055254931377587170923693 17270720599266595189096385)
    ·
      refine ⟨12953040449449946391822289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17270720599266595189096385 12953040449449946391822289)
      ·
        refine ⟨9714780337087459793866717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12953040449449946391822289 9714780337087459793866717)
        ·
          refine ⟨3643042626407797422700019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9714780337087459793866717 3643042626407797422700019)
          ·
            refine ⟨5464563939611696134050029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3643042626407797422700019 5464563939611696134050029)
            ·
              refine ⟨2049211477354386050268761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5464563939611696134050029 2049211477354386050268761)
              ·
                refine ⟨1536908608015789537701571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2049211477354386050268761 1536908608015789537701571)
                ·
                  refine ⟨2305362912023684306552357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1536908608015789537701571 2305362912023684306552357)
                  ·
                    refine ⟨432255546004440807478567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2305362912023684306552357 432255546004440807478567)
                    ·
                      rfl

theorem cell23_2525444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3, 2, 1, 4].length) (baseStart_2525444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2525444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2525444 prefixEnd_2525444 := by exact prefixLift 2525444
  have htrace : WordTrace (prefixWord ++ tailWord_2525444) baseStart_2525444 baseEnd_2525444 := by
    simpa [prefixWord, tailWord_2525444, baseEnd_2525444] using wordTrace_append hprefix tailTrace_2525444
  have hstable : (prefixWord ++ tailWord_2525444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525444).length < 2 ^ (prefixWord ++ tailWord_2525444).sum := by decide
  have hdescent : baseEnd_2525444 < baseStart_2525444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525450 : List Nat := [3, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3]
def baseStart_2525450 : Nat := 118140960795 + 2525450 * 2 ^ 59
def prefixEnd_2525450 : Nat := 4983230072969 + 3 ^ 40 * 2525450 * 2
def baseEnd_2525450 : Nat := 1296769718897249398960673

theorem tailTrace_2525450 : CollatzResearch.WordTrace tailWord_2525450 prefixEnd_2525450 1296769718897249398960673 := by
  unfold tailWord_2525450
  simp only [CollatzResearch.WordTrace]
  refine ⟨23027682175183359341641451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61407152467155624911043869 23027682175183359341641451)
  ·
    refine ⟨34541523262775039012462177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23027682175183359341641451 34541523262775039012462177)
    ·
      refine ⟨25906142447081279259346633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34541523262775039012462177 25906142447081279259346633)
      ·
        refine ⟨19429606835310959444509975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25906142447081279259346633 19429606835310959444509975)
        ·
          refine ⟨29144410252966439166764963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19429606835310959444509975 29144410252966439166764963)
          ·
            refine ⟨43716615379449658750147445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29144410252966439166764963 43716615379449658750147445)
            ·
              refine ⟨4098432691823405507826323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43716615379449658750147445 4098432691823405507826323)
              ·
                refine ⟨6147649037735108261739485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4098432691823405507826323 6147649037735108261739485)
                ·
                  refine ⟨2305368389150665598152307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6147649037735108261739485 2305368389150665598152307)
                  ·
                    refine ⟨3458052583725998397228461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2305368389150665598152307 3458052583725998397228461)
                    ·
                      refine ⟨1296769718897249398960673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3458052583725998397228461 1296769718897249398960673)
                      ·
                        rfl

theorem cell23_2525450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3].length) (baseStart_2525450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2525450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2525450 prefixEnd_2525450 := by exact prefixLift 2525450
  have htrace : WordTrace (prefixWord ++ tailWord_2525450) baseStart_2525450 baseEnd_2525450 := by
    simpa [prefixWord, tailWord_2525450, baseEnd_2525450] using wordTrace_append hprefix tailTrace_2525450
  have hstable : (prefixWord ++ tailWord_2525450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525450).length < 2 ^ (prefixWord ++ tailWord_2525450).sum := by decide
  have hdescent : baseEnd_2525450 < baseStart_2525450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525473 : List Nat := [1, 2, 3, 2, 1, 1, 2, 1, 2, 6, 2]
def baseStart_2525473 : Nat := 118140960795 + 2525473 * 2 ^ 59
def prefixEnd_2525473 : Nat := 4983230072969 + 3 ^ 40 * 2525473 * 2
def baseEnd_2525473 : Nat := 1296781528952302808973067

theorem tailTrace_2525473 : CollatzResearch.WordTrace tailWord_2525473 prefixEnd_2525473 1296781528952302808973067 := by
  unfold tailWord_2525473
  simp only [CollatzResearch.WordTrace]
  refine ⟨92111567579650112294653073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61407711719766741529768715 92111567579650112294653073)
  ·
    refine ⟨69083675684737584220989805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92111567579650112294653073 69083675684737584220989805)
    ·
      refine ⟨25906378381776594082871177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69083675684737584220989805 25906378381776594082871177)
      ·
        refine ⟨19429783786332445562153383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25906378381776594082871177 19429783786332445562153383)
        ·
          refine ⟨29144675679498668343230075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19429783786332445562153383 29144675679498668343230075)
          ·
            refine ⟨43717013519248002514845113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29144675679498668343230075 43717013519248002514845113)
            ·
              refine ⟨32787760139436001886133835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43717013519248002514845113 32787760139436001886133835)
              ·
                refine ⟨49181640209154002829200753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32787760139436001886133835 49181640209154002829200753)
                ·
                  refine ⟨36886230156865502121900565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49181640209154002829200753 36886230156865502121900565)
                  ·
                    refine ⟨1729042038603070411964089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 36886230156865502121900565 1729042038603070411964089)
                    ·
                      refine ⟨1296781528952302808973067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1729042038603070411964089 1296781528952302808973067)
                      ·
                        rfl

theorem cell23_2525473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 6, 2].length) (baseStart_2525473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2525473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2525473 prefixEnd_2525473 := by exact prefixLift 2525473
  have htrace : WordTrace (prefixWord ++ tailWord_2525473) baseStart_2525473 baseEnd_2525473 := by
    simpa [prefixWord, tailWord_2525473, baseEnd_2525473] using wordTrace_append hprefix tailTrace_2525473
  have hstable : (prefixWord ++ tailWord_2525473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525473).length < 2 ^ (prefixWord ++ tailWord_2525473).sum := by decide
  have hdescent : baseEnd_2525473 < baseStart_2525473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525477 : List Nat := [1, 3, 1, 2, 5, 1, 2, 1, 2, 3, 2]
def baseStart_2525477 : Nat := 118140960795 + 2525477 * 2 ^ 59
def prefixEnd_2525477 : Nat := 4983230072969 + 3 ^ 40 * 2525477 * 2
def baseEnd_2525477 : Nat := 1296783582874920793323049

theorem tailTrace_2525477 : CollatzResearch.WordTrace tailWord_2525477 prefixEnd_2525477 1296783582874920793323049 := by
  unfold tailWord_2525477
  simp only [CollatzResearch.WordTrace]
  refine ⟨92111713471635620977798685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61407808981090413985199123 92111713471635620977798685)
  ·
    refine ⟨34541892551863357866674507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92111713471635620977798685 34541892551863357866674507)
    ·
      refine ⟨51812838827795036800011761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34541892551863357866674507 51812838827795036800011761)
      ·
        refine ⟨38859629120846277600008821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51812838827795036800011761 38859629120846277600008821)
        ·
          refine ⟨3643090230079338525000827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38859629120846277600008821 3643090230079338525000827)
          ·
            refine ⟨5464635345119007787501241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3643090230079338525000827 5464635345119007787501241)
            ·
              refine ⟨4098476508839255840625931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5464635345119007787501241 4098476508839255840625931)
              ·
                refine ⟨6147714763258883760938897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4098476508839255840625931 6147714763258883760938897)
                ·
                  refine ⟨4610786072444162820704173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6147714763258883760938897 4610786072444162820704173)
                  ·
                    refine ⟨1729044777166561057764065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4610786072444162820704173 1729044777166561057764065)
                    ·
                      refine ⟨1296783582874920793323049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1729044777166561057764065 1296783582874920793323049)
                      ·
                        rfl

theorem cell23_2525477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 1, 2, 3, 2].length) (baseStart_2525477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2525477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2525477 prefixEnd_2525477 := by exact prefixLift 2525477
  have htrace : WordTrace (prefixWord ++ tailWord_2525477) baseStart_2525477 baseEnd_2525477 := by
    simpa [prefixWord, tailWord_2525477, baseEnd_2525477] using wordTrace_append hprefix tailTrace_2525477
  have hstable : (prefixWord ++ tailWord_2525477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525477).length < 2 ^ (prefixWord ++ tailWord_2525477).sum := by decide
  have hdescent : baseEnd_2525477 < baseStart_2525477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525500 : List Nat := [2, 2, 2, 2, 1, 2, 4, 2, 2, 4]
def baseStart_2525500 : Nat := 118140960795 + 2525500 * 2 ^ 59
def prefixEnd_2525500 : Nat := 4983230072969 + 3 ^ 40 * 2525500 * 2
def baseEnd_2525500 : Nat := 432265130976658067778481

theorem tailTrace_2525500 : CollatzResearch.WordTrace tailWord_2525500 prefixEnd_2525500 432265130976658067778481 := by
  unfold tailWord_2525500
  simp only [CollatzResearch.WordTrace]
  refine ⟨46056276175276147952942977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61408368233701530603923969 46056276175276147952942977)
  ·
    refine ⟨34542207131457110964707233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46056276175276147952942977 34542207131457110964707233)
    ·
      refine ⟨25906655348592833223530425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34542207131457110964707233 25906655348592833223530425)
      ·
        refine ⟨19429991511444624917647819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25906655348592833223530425 19429991511444624917647819)
        ·
          refine ⟨29144987267166937376471729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19429991511444624917647819 29144987267166937376471729)
          ·
            refine ⟨21858740450375203032353797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29144987267166937376471729 21858740450375203032353797)
            ·
              refine ⟨4098513834445350568566337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21858740450375203032353797 4098513834445350568566337)
              ·
                refine ⟨3073885375834012926424753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4098513834445350568566337 3073885375834012926424753)
                ·
                  refine ⟨2305414031875509694818565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3073885375834012926424753 2305414031875509694818565)
                  ·
                    refine ⟨432265130976658067778481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2305414031875509694818565 432265130976658067778481)
                    ·
                      rfl

theorem cell23_2525500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 2, 2, 4].length) (baseStart_2525500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2525500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2525500 prefixEnd_2525500 := by exact prefixLift 2525500
  have htrace : WordTrace (prefixWord ++ tailWord_2525500) baseStart_2525500 baseEnd_2525500 := by
    simpa [prefixWord, tailWord_2525500, baseEnd_2525500] using wordTrace_append hprefix tailTrace_2525500
  have hstable : (prefixWord ++ tailWord_2525500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525500).length < 2 ^ (prefixWord ++ tailWord_2525500).sum := by decide
  have hdescent : baseEnd_2525500 < baseStart_2525500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525540 : List Nat := [2, 3, 1, 1, 3, 1, 2, 2, 4, 1, 3]
def baseStart_2525540 : Nat := 118140960795 + 2525540 * 2 ^ 59
def prefixEnd_2525540 : Nat := 4983230072969 + 3 ^ 40 * 2525540 * 2
def baseEnd_2525540 : Nat := 1296815932156154046835259

theorem tailTrace_2525540 : CollatzResearch.WordTrace tailWord_2525540 prefixEnd_2525540 1296815932156154046835259 := by
  unfold tailWord_2525540
  simp only [CollatzResearch.WordTrace]
  refine ⟨46057005635203691368671037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61409340846938255158228049 46057005635203691368671037)
  ·
    refine ⟨17271377113201384263251639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46057005635203691368671037 17271377113201384263251639)
    ·
      refine ⟨25907065669802076394877459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17271377113201384263251639 25907065669802076394877459)
      ·
        refine ⟨38860598504703114592316189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25907065669802076394877459 38860598504703114592316189)
        ·
          refine ⟨14572724439263667972118571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38860598504703114592316189 14572724439263667972118571)
          ·
            refine ⟨21859086658895501958177857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14572724439263667972118571 21859086658895501958177857)
            ·
              refine ⟨16394314994171626468633393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21859086658895501958177857 16394314994171626468633393)
              ·
                refine ⟨12295736245628719851475045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16394314994171626468633393 12295736245628719851475045)
                ·
                  refine ⟨2305450546055384972151571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12295736245628719851475045 2305450546055384972151571)
                  ·
                    refine ⟨3458175819083077458227357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2305450546055384972151571 3458175819083077458227357)
                    ·
                      refine ⟨1296815932156154046835259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3458175819083077458227357 1296815932156154046835259)
                      ·
                        rfl

theorem cell23_2525540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 4, 1, 3].length) (baseStart_2525540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2525540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2525540 prefixEnd_2525540 := by exact prefixLift 2525540
  have htrace : WordTrace (prefixWord ++ tailWord_2525540) baseStart_2525540 baseEnd_2525540 := by
    simpa [prefixWord, tailWord_2525540, baseEnd_2525540] using wordTrace_append hprefix tailTrace_2525540
  have hstable : (prefixWord ++ tailWord_2525540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525540).length < 2 ^ (prefixWord ++ tailWord_2525540).sum := by decide
  have hdescent : baseEnd_2525540 < baseStart_2525540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525544 : List Nat := [2, 1, 4, 2, 2, 3, 2, 1, 1, 2, 3]
def baseStart_2525544 : Nat := 118140960795 + 2525544 * 2 ^ 59
def prefixEnd_2525544 : Nat := 4983230072969 + 3 ^ 40 * 2525544 * 2
def baseEnd_2525544 : Nat := 1296817986078772031185241

theorem tailTrace_2525544 : CollatzResearch.WordTrace tailWord_2525544 prefixEnd_2525544 1296817986078772031185241 := by
  unfold tailWord_2525544
  simp only [CollatzResearch.WordTrace]
  refine ⟨46057078581196445710243843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61409438108261927613658457 46057078581196445710243843)
  ·
    refine ⟨69085617871794668565365765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46057078581196445710243843 69085617871794668565365765)
    ·
      refine ⟨12953553350961500356006081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69085617871794668565365765 12953553350961500356006081)
      ·
        refine ⟨9715165013221125267004561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12953553350961500356006081 9715165013221125267004561)
        ·
          refine ⟨7286373759915843950253421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9715165013221125267004561 7286373759915843950253421)
          ·
            refine ⟨2732390159968441481345033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7286373759915843950253421 2732390159968441481345033)
            ·
              refine ⟨2049292619976331111008775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2732390159968441481345033 2049292619976331111008775)
              ·
                refine ⟨3073938929964496666513163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2049292619976331111008775 3073938929964496666513163)
                ·
                  refine ⟨4610908394946744999769745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3073938929964496666513163 4610908394946744999769745)
                  ·
                    refine ⟨3458181296210058749827309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4610908394946744999769745 3458181296210058749827309)
                    ·
                      refine ⟨1296817986078772031185241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3458181296210058749827309 1296817986078772031185241)
                      ·
                        rfl

theorem cell23_2525544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_2525544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2525544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2525544 prefixEnd_2525544 := by exact prefixLift 2525544
  have htrace : WordTrace (prefixWord ++ tailWord_2525544) baseStart_2525544 baseEnd_2525544 := by
    simpa [prefixWord, tailWord_2525544, baseEnd_2525544] using wordTrace_append hprefix tailTrace_2525544
  have hstable : (prefixWord ++ tailWord_2525544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525544).length < 2 ^ (prefixWord ++ tailWord_2525544).sum := by decide
  have hdescent : baseEnd_2525544 < baseStart_2525544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525557 : List Nat := [1, 3, 4, 1, 2, 2, 1, 1, 4, 1, 3]
def baseStart_2525557 : Nat := 118140960795 + 2525557 * 2 ^ 59
def prefixEnd_2525557 : Nat := 4983230072969 + 3 ^ 40 * 2525557 * 2
def baseEnd_2525557 : Nat := 1296824661327280480322681

theorem tailTrace_2525557 : CollatzResearch.WordTrace tailWord_2525557 prefixEnd_2525557 1296824661327280480322681 := by
  unfold tailWord_2525557
  simp only [CollatzResearch.WordTrace]
  refine ⟨92114631311345794640710925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61409754207563863093807283 92114631311345794640710925)
  ·
    refine ⟨34542986741754672990266597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92114631311345794640710925 34542986741754672990266597)
    ·
      refine ⟨6476810014079001185674987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34542986741754672990266597 6476810014079001185674987)
      ·
        refine ⟨9715215021118501778512481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6476810014079001185674987 9715215021118501778512481)
        ·
          refine ⟨7286411265838876333884361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9715215021118501778512481 7286411265838876333884361)
          ·
            refine ⟨5464808449379157250413271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7286411265838876333884361 5464808449379157250413271)
            ·
              refine ⟨8197212674068735875619907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5464808449379157250413271 8197212674068735875619907)
              ·
                refine ⟨12295819011103103813429861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8197212674068735875619907 12295819011103103813429861)
                ·
                  refine ⟨2305466064581831965018099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12295819011103103813429861 2305466064581831965018099)
                  ·
                    refine ⟨3458199096872747947527149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2305466064581831965018099 3458199096872747947527149)
                    ·
                      refine ⟨1296824661327280480322681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3458199096872747947527149 1296824661327280480322681)
                      ·
                        rfl

theorem cell23_2525557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_2525557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2525557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2525557 prefixEnd_2525557 := by exact prefixLift 2525557
  have htrace : WordTrace (prefixWord ++ tailWord_2525557) baseStart_2525557 baseEnd_2525557 := by
    simpa [prefixWord, tailWord_2525557, baseEnd_2525557] using wordTrace_append hprefix tailTrace_2525557
  have hstable : (prefixWord ++ tailWord_2525557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525557).length < 2 ^ (prefixWord ++ tailWord_2525557).sum := by decide
  have hdescent : baseEnd_2525557 < baseStart_2525557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525630 : List Nat := [4, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3]
def baseStart_2525630 : Nat := 118140960795 + 2525630 * 2 ^ 59
def prefixEnd_2525630 : Nat := 4983230072969 + 3 ^ 40 * 2525630 * 2
def baseEnd_2525630 : Nat := 1296862145415058694709845

theorem tailTrace_2525630 : CollatzResearch.WordTrace tailWord_2525630 prefixEnd_2525630 1296862145415058694709845 := by
  unfold tailWord_2525630
  simp only [CollatzResearch.WordTrace]
  refine ⟨11514661730010166013514793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61411529226720885405412229 11514661730010166013514793)
  ·
    refine ⟨8635996297507624510136095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11514661730010166013514793 8635996297507624510136095)
    ·
      refine ⟨12953994446261436765204143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8635996297507624510136095 12953994446261436765204143)
      ·
        refine ⟨19430991669392155147806215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12953994446261436765204143 19430991669392155147806215)
        ·
          refine ⟨29146487504088232721709323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19430991669392155147806215 29146487504088232721709323)
          ·
            refine ⟨43719731256132349082563985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29146487504088232721709323 43719731256132349082563985)
            ·
              refine ⟨32789798442099261811922989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43719731256132349082563985 32789798442099261811922989)
              ·
                refine ⟨12296174415787223179471121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32789798442099261811922989 12296174415787223179471121)
                ·
                  refine ⟨9222130811840417384603341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12296174415787223179471121 9222130811840417384603341)
                  ·
                    refine ⟨3458299054440156519226253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9222130811840417384603341 3458299054440156519226253)
                    ·
                      refine ⟨1296862145415058694709845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3458299054440156519226253 1296862145415058694709845)
                      ·
                        rfl

theorem cell23_2525630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_2525630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2525630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2525630 prefixEnd_2525630 := by exact prefixLift 2525630
  have htrace : WordTrace (prefixWord ++ tailWord_2525630) baseStart_2525630 baseEnd_2525630 := by
    simpa [prefixWord, tailWord_2525630, baseEnd_2525630] using wordTrace_append hprefix tailTrace_2525630
  have hstable : (prefixWord ++ tailWord_2525630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525630).length < 2 ^ (prefixWord ++ tailWord_2525630).sum := by decide
  have hdescent : baseEnd_2525630 < baseStart_2525630 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525680 : List Nat := [2, 1, 1, 1, 3, 3, 2, 3, 3, 4]
def baseStart_2525680 : Nat := 118140960795 + 2525680 * 2 ^ 59
def prefixEnd_2525680 : Nat := 4983230072969 + 3 ^ 40 * 2525680 * 2
def baseEnd_2525680 : Nat := 432295939815927833028205

theorem tailTrace_2525680 : CollatzResearch.WordTrace tailWord_2525680 prefixEnd_2525680 432295939815927833028205 := by
  unfold tailWord_2525680
  simp only [CollatzResearch.WordTrace]
  refine ⟨46059558744950093323719247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61412744993266791098292329 46059558744950093323719247)
  ·
    refine ⟨69089338117425139985578871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46059558744950093323719247 69089338117425139985578871)
    ·
      refine ⟨103634007176137709978368307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69089338117425139985578871 103634007176137709978368307)
      ·
        refine ⟨155451010764206564967552461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103634007176137709978368307 155451010764206564967552461)
        ·
          refine ⟨58294129036577461862832173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155451010764206564967552461 58294129036577461862832173)
          ·
            refine ⟨21860298388716548198562065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58294129036577461862832173 21860298388716548198562065)
            ·
              refine ⟨16395223791537411148921549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21860298388716548198562065 16395223791537411148921549)
              ·
                refine ⟨6148208921826529180845581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16395223791537411148921549 6148208921826529180845581)
                ·
                  refine ⟨2305578345684948442817093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6148208921826529180845581 2305578345684948442817093)
                  ·
                    refine ⟨432295939815927833028205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2305578345684948442817093 432295939815927833028205)
                    ·
                      rfl

theorem cell23_2525680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3, 3, 4].length) (baseStart_2525680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2525680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2525680 prefixEnd_2525680 := by exact prefixLift 2525680
  have htrace : WordTrace (prefixWord ++ tailWord_2525680) baseStart_2525680 baseEnd_2525680 := by
    simpa [prefixWord, tailWord_2525680, baseEnd_2525680] using wordTrace_append hprefix tailTrace_2525680
  have hstable : (prefixWord ++ tailWord_2525680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525680).length < 2 ^ (prefixWord ++ tailWord_2525680).sum := by decide
  have hdescent : baseEnd_2525680 < baseStart_2525680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525697 : List Nat := [1, 2, 4, 1, 3, 2, 1, 2, 3, 4]
def baseStart_2525697 : Nat := 118140960795 + 2525697 * 2 ^ 59
def prefixEnd_2525697 : Nat := 4983230072969 + 3 ^ 40 * 2525697 * 2
def baseEnd_2525697 : Nat := 432298849539636644190679

theorem tailTrace_2525697 : CollatzResearch.WordTrace tailWord_2525697 prefixEnd_2525697 432298849539636644190679 := by
  unfold tailWord_2525697
  simp only [CollatzResearch.WordTrace]
  refine ⟨92119737530838598550807345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61413158353892399033871563 92119737530838598550807345)
  ·
    refine ⟨69089803148128948913105509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92119737530838598550807345 69089803148128948913105509)
    ·
      refine ⟨12954338090274177921207283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69089803148128948913105509 12954338090274177921207283)
      ·
        refine ⟨19431507135411266881810925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12954338090274177921207283 19431507135411266881810925)
        ·
          refine ⟨7286815175779225080679097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19431507135411266881810925 7286815175779225080679097)
          ·
            refine ⟨5465111381834418810509323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7286815175779225080679097 5465111381834418810509323)
            ·
              refine ⟨8197667072751628215763985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5465111381834418810509323 8197667072751628215763985)
              ·
                refine ⟨6148250304563721161822989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8197667072751628215763985 6148250304563721161822989)
                ·
                  refine ⟨2305593864211395435683621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6148250304563721161822989 2305593864211395435683621)
                  ·
                    refine ⟨432298849539636644190679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2305593864211395435683621 432298849539636644190679)
                    ·
                      rfl

theorem cell23_2525697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_2525697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2525697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2525697 prefixEnd_2525697 := by exact prefixLift 2525697
  have htrace : WordTrace (prefixWord ++ tailWord_2525697) baseStart_2525697 baseEnd_2525697 := by
    simpa [prefixWord, tailWord_2525697, baseEnd_2525697] using wordTrace_append hprefix tailTrace_2525697
  have hstable : (prefixWord ++ tailWord_2525697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525697).length < 2 ^ (prefixWord ++ tailWord_2525697).sum := by decide
  have hdescent : baseEnd_2525697 < baseStart_2525697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525707 : List Nat := [1, 1, 1, 1, 7, 1, 3, 1, 2, 2, 3]
def baseStart_2525707 : Nat := 118140960795 + 2525707 * 2 ^ 59
def prefixEnd_2525707 : Nat := 4983230072969 + 3 ^ 40 * 2525707 * 2
def baseEnd_2525707 : Nat := 1296901683425454893446991

theorem tailTrace_2525707 : CollatzResearch.WordTrace tailWord_2525707 prefixEnd_2525707 1296901683425454893446991 := by
  unfold tailWord_2525707
  simp only [CollatzResearch.WordTrace]
  refine ⟨92120102260802370258671375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61413401507201580172447583 92120102260802370258671375)
  ·
    refine ⟨138180153391203555388007063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92120102260802370258671375 138180153391203555388007063)
    ·
      refine ⟨207270230086805333082010595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138180153391203555388007063 207270230086805333082010595)
      ·
        refine ⟨310905345130207999623015893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207270230086805333082010595 310905345130207999623015893)
        ·
          refine ⟨7286844026489249991164435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 310905345130207999623015893 7286844026489249991164435)
          ·
            refine ⟨10930266039733874986746653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7286844026489249991164435 10930266039733874986746653)
            ·
              refine ⟨4098849764900203120029995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10930266039733874986746653 4098849764900203120029995)
              ·
                refine ⟨6148274647350304680044993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4098849764900203120029995 6148274647350304680044993)
                ·
                  refine ⟨4611205985512728510033745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6148274647350304680044993 4611205985512728510033745)
                  ·
                    refine ⟨3458404489134546382525309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4611205985512728510033745 3458404489134546382525309)
                    ·
                      refine ⟨1296901683425454893446991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3458404489134546382525309 1296901683425454893446991)
                      ·
                        rfl

theorem cell23_2525707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 1, 2, 2, 3].length) (baseStart_2525707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2525707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2525707 prefixEnd_2525707 := by exact prefixLift 2525707
  have htrace : WordTrace (prefixWord ++ tailWord_2525707) baseStart_2525707 baseEnd_2525707 := by
    simpa [prefixWord, tailWord_2525707, baseEnd_2525707] using wordTrace_append hprefix tailTrace_2525707
  have hstable : (prefixWord ++ tailWord_2525707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525707).length < 2 ^ (prefixWord ++ tailWord_2525707).sum := by decide
  have hdescent : baseEnd_2525707 < baseStart_2525707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525757 : List Nat := [1, 4, 1, 3, 2, 1, 1, 4, 1, 5]
def baseStart_2525757 : Nat := 118140960795 + 2525757 * 2 ^ 59
def prefixEnd_2525757 : Nat := 4983230072969 + 3 ^ 40 * 2525757 * 2
def baseEnd_2525757 : Nat := 432309119152726565940587

theorem tailTrace_2525757 : CollatzResearch.WordTrace tailWord_2525757 prefixEnd_2525757 432309119152726565940587 := by
  unfold tailWord_2525757
  simp only [CollatzResearch.WordTrace]
  refine ⟨92121925910621228797991525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61414617273747485865327683 92121925910621228797991525)
  ·
    refine ⟨17272861108241480399623411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92121925910621228797991525 17272861108241480399623411)
    ·
      refine ⟨25909291662362220599435117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17272861108241480399623411 25909291662362220599435117)
      ·
        refine ⟨9715984373385832724788169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25909291662362220599435117 9715984373385832724788169)
        ·
          refine ⟨7286988280039374543591127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9715984373385832724788169 7286988280039374543591127)
          ·
            refine ⟨10930482420059061815386691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7286988280039374543591127 10930482420059061815386691)
            ·
              refine ⟨16395723630088592723080037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10930482420059061815386691 16395723630088592723080037)
              ·
                refine ⟨3074198180641611135577507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16395723630088592723080037 3074198180641611135577507)
                ·
                  refine ⟨4611297270962416703366261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3074198180641611135577507 4611297270962416703366261)
                  ·
                    refine ⟨432309119152726565940587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4611297270962416703366261 432309119152726565940587)
                    ·
                      rfl

theorem cell23_2525757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 4, 1, 5].length) (baseStart_2525757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2525757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2525757 prefixEnd_2525757 := by exact prefixLift 2525757
  have htrace : WordTrace (prefixWord ++ tailWord_2525757) baseStart_2525757 baseEnd_2525757 := by
    simpa [prefixWord, tailWord_2525757, baseEnd_2525757] using wordTrace_append hprefix tailTrace_2525757
  have hstable : (prefixWord ++ tailWord_2525757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525757).length < 2 ^ (prefixWord ++ tailWord_2525757).sum := by decide
  have hdescent : baseEnd_2525757 < baseStart_2525757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525760 : List Nat := [2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 4]
def baseStart_2525760 : Nat := 118140960795 + 2525760 * 2 ^ 59
def prefixEnd_2525760 : Nat := 4983230072969 + 3 ^ 40 * 2525760 * 2
def baseEnd_2525760 : Nat := 1296928897900143186084247

theorem tailTrace_2525760 : CollatzResearch.WordTrace tailWord_2525760 prefixEnd_2525760 1296928897900143186084247 := by
  unfold tailWord_2525760
  simp only [CollatzResearch.WordTrace]
  refine ⟨46061017664805180155175367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61414690219740240206900489 46061017664805180155175367)
  ·
    refine ⟨69091526497207770232763051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46061017664805180155175367 69091526497207770232763051)
    ·
      refine ⟨103637289745811655349144577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69091526497207770232763051 103637289745811655349144577)
      ·
        refine ⟨77727967309358741511858433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103637289745811655349144577 77727967309358741511858433)
        ·
          refine ⟨58295975482019056133893825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77727967309358741511858433 58295975482019056133893825)
          ·
            refine ⟨43721981611514292100420369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58295975482019056133893825 43721981611514292100420369)
            ·
              refine ⟨32791486208635719075315277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43721981611514292100420369 32791486208635719075315277)
              ·
                refine ⟨12296807328238394653243229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32791486208635719075315277 12296807328238394653243229)
                ·
                  refine ⟨4611302748089397994966211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12296807328238394653243229 4611302748089397994966211)
                  ·
                    refine ⟨6916954122134096992449317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4611302748089397994966211 6916954122134096992449317)
                    ·
                      refine ⟨1296928897900143186084247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6916954122134096992449317 1296928897900143186084247)
                      ·
                        rfl

theorem cell23_2525760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 4].length) (baseStart_2525760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2525760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2525760 prefixEnd_2525760 := by exact prefixLift 2525760
  have htrace : WordTrace (prefixWord ++ tailWord_2525760) baseStart_2525760 baseEnd_2525760 := by
    simpa [prefixWord, tailWord_2525760, baseEnd_2525760] using wordTrace_append hprefix tailTrace_2525760
  have hstable : (prefixWord ++ tailWord_2525760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525760).length < 2 ^ (prefixWord ++ tailWord_2525760).sum := by decide
  have hdescent : baseEnd_2525760 < baseStart_2525760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525777 : List Nat := [1, 2, 2, 1, 3, 3, 2, 3, 1, 1, 4]
def baseStart_2525777 : Nat := 118140960795 + 2525777 * 2 ^ 59
def prefixEnd_2525777 : Nat := 4983230072969 + 3 ^ 40 * 2525777 * 2
def baseEnd_2525777 : Nat := 1296937627071269619571669

theorem tailTrace_2525777 : CollatzResearch.WordTrace tailWord_2525777 prefixEnd_2525777 1296937627071269619571669 := by
  unfold tailWord_2525777
  simp only [CollatzResearch.WordTrace]
  refine ⟨92122655370548772213719585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61415103580365848142479723 92122655370548772213719585)
  ·
    refine ⟨69091991527911579160289689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92122655370548772213719585 69091991527911579160289689)
    ·
      refine ⟨51818993645933684370217267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69091991527911579160289689 51818993645933684370217267)
      ·
        refine ⟨77728490468900526555325901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51818993645933684370217267 77728490468900526555325901)
        ·
          refine ⟨29148183925837697458247213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77728490468900526555325901 29148183925837697458247213)
          ·
            refine ⟨10930568972189136546842705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29148183925837697458247213 10930568972189136546842705)
            ·
              refine ⟨8197926729141852410132029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10930568972189136546842705 8197926729141852410132029)
              ·
                refine ⟨3074222523428194653799511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8197926729141852410132029 3074222523428194653799511)
                ·
                  refine ⟨4611333785142291980699267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3074222523428194653799511 4611333785142291980699267)
                  ·
                    refine ⟨6917000677713437971048901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4611333785142291980699267 6917000677713437971048901)
                    ·
                      refine ⟨1296937627071269619571669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6917000677713437971048901 1296937627071269619571669)
                      ·
                        rfl

theorem cell23_2525777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 3, 1, 1, 4].length) (baseStart_2525777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2525777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2525777 prefixEnd_2525777 := by exact prefixLift 2525777
  have htrace : WordTrace (prefixWord ++ tailWord_2525777) baseStart_2525777 baseEnd_2525777 := by
    simpa [prefixWord, tailWord_2525777, baseEnd_2525777] using wordTrace_append hprefix tailTrace_2525777
  have hstable : (prefixWord ++ tailWord_2525777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525777).length < 2 ^ (prefixWord ++ tailWord_2525777).sum := by decide
  have hdescent : baseEnd_2525777 < baseStart_2525777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525788 : List Nat := [2, 2, 4, 1, 4, 1, 1, 1, 3, 1, 3]
def baseStart_2525788 : Nat := 118140960795 + 2525788 * 2 ^ 59
def prefixEnd_2525788 : Nat := 4983230072969 + 3 ^ 40 * 2525788 * 2
def baseEnd_2525788 : Nat := 1296943275358469076534119

theorem tailTrace_2525788 : CollatzResearch.WordTrace tailWord_2525788 prefixEnd_2525788 1296943275358469076534119 := by
  unfold tailWord_2525788
  simp only [CollatzResearch.WordTrace]
  refine ⟨46061528286754460546185009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61415371049005947394913345 46061528286754460546185009)
  ·
    refine ⟨34546146215065845409638757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46061528286754460546185009 34546146215065845409638757)
    ·
      refine ⟨6477402415324846014307267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34546146215065845409638757 6477402415324846014307267)
      ·
        refine ⟨9716103622987269021460901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6477402415324846014307267 9716103622987269021460901)
        ·
          refine ⟨1821769429310112941523919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9716103622987269021460901 1821769429310112941523919)
          ·
            refine ⟨2732654143965169412285879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1821769429310112941523919 2732654143965169412285879)
            ·
              refine ⟨4098981215947754118428819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2732654143965169412285879 4098981215947754118428819)
              ·
                refine ⟨6148471823921631177643229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4098981215947754118428819 6148471823921631177643229)
                ·
                  refine ⟨2305676933970611691616211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6148471823921631177643229 2305676933970611691616211)
                  ·
                    refine ⟨3458515400955917537424317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2305676933970611691616211 3458515400955917537424317)
                    ·
                      refine ⟨1296943275358469076534119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3458515400955917537424317 1296943275358469076534119)
                      ·
                        rfl

theorem cell23_2525788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_2525788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2525788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2525788 prefixEnd_2525788 := by exact prefixLift 2525788
  have htrace : WordTrace (prefixWord ++ tailWord_2525788) baseStart_2525788 baseEnd_2525788 := by
    simpa [prefixWord, tailWord_2525788, baseEnd_2525788] using wordTrace_append hprefix tailTrace_2525788
  have hstable : (prefixWord ++ tailWord_2525788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525788).length < 2 ^ (prefixWord ++ tailWord_2525788).sum := by decide
  have hdescent : baseEnd_2525788 < baseStart_2525788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525804 : List Nat := [2, 2, 1, 1, 3, 1, 6, 1, 2, 4]
def baseStart_2525804 : Nat := 118140960795 + 2525804 * 2 ^ 59
def prefixEnd_2525804 : Nat := 4983230072969 + 3 ^ 40 * 2525804 * 2
def baseEnd_2525804 : Nat := 432317163682980337978015

theorem tailTrace_2525804 : CollatzResearch.WordTrace tailWord_2525804 prefixEnd_2525804 432317163682980337978015 := by
  unfold tailWord_2525804
  simp only [CollatzResearch.WordTrace]
  refine ⟨46061820070725477912476233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61415760094300637216634977 46061820070725477912476233)
  ·
    refine ⟨34546365053044108434357175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46061820070725477912476233 34546365053044108434357175)
    ·
      refine ⟨51819547579566162651535763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34546365053044108434357175 51819547579566162651535763)
      ·
        refine ⟨77729321369349243977303645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51819547579566162651535763 77729321369349243977303645)
        ·
          refine ⟨29148495513505966491488867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77729321369349243977303645 29148495513505966491488867)
          ·
            refine ⟨43722743270258949737233301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29148495513505966491488867 43722743270258949737233301)
            ·
              refine ⟨2049503590793388268932811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 43722743270258949737233301 2049503590793388268932811)
              ·
                refine ⟨3074255386190082403399217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2049503590793388268932811 3074255386190082403399217)
                ·
                  refine ⟨2305691539642561802549413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3074255386190082403399217 2305691539642561802549413)
                  ·
                    refine ⟨432317163682980337978015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2305691539642561802549413 432317163682980337978015)
                    ·
                      rfl

theorem cell23_2525804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 4].length) (baseStart_2525804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2525804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2525804 prefixEnd_2525804 := by exact prefixLift 2525804
  have htrace : WordTrace (prefixWord ++ tailWord_2525804) baseStart_2525804 baseEnd_2525804 := by
    simpa [prefixWord, tailWord_2525804, baseEnd_2525804] using wordTrace_append hprefix tailTrace_2525804
  have hstable : (prefixWord ++ tailWord_2525804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525804).length < 2 ^ (prefixWord ++ tailWord_2525804).sum := by decide
  have hdescent : baseEnd_2525804 < baseStart_2525804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525827 : List Nat := [1, 1, 1, 3, 3, 1, 2, 1, 6, 1, 3]
def baseStart_2525827 : Nat := 118140960795 + 2525827 * 2 ^ 59
def prefixEnd_2525827 : Nat := 4983230072969 + 3 ^ 40 * 2525827 * 2
def baseEnd_2525827 : Nat := 1296963301103994423946439

theorem tailTrace_2525827 : CollatzResearch.WordTrace tailWord_2525827 prefixEnd_2525827 1296963301103994423946439 := by
  unfold tailWord_2525827
  simp only [CollatzResearch.WordTrace]
  refine ⟨92124479020367630753039735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61416319346911753835359823 92124479020367630753039735)
  ·
    refine ⟨138186718530551446129559603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92124479020367630753039735 138186718530551446129559603)
    ·
      refine ⟨207280077795827169194339405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138186718530551446129559603 207280077795827169194339405)
      ·
        refine ⟨77730029173435188447877277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 207280077795827169194339405 77730029173435188447877277)
        ·
          refine ⟨29148760940038195667953979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77730029173435188447877277 29148760940038195667953979)
          ·
            refine ⟨43723141410057293501930969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29148760940038195667953979 43723141410057293501930969)
            ·
              refine ⟨32792356057542970126448227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43723141410057293501930969 32792356057542970126448227)
              ·
                refine ⟨49188534086314455189672341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32792356057542970126448227 49188534086314455189672341)
                ·
                  refine ⟨2305712535295990087015891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 49188534086314455189672341 2305712535295990087015891)
                  ·
                    refine ⟨3458568802943985130523837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2305712535295990087015891 3458568802943985130523837)
                    ·
                      refine ⟨1296963301103994423946439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3458568802943985130523837 1296963301103994423946439)
                      ·
                        rfl

theorem cell23_2525827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 6, 1, 3].length) (baseStart_2525827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2525827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2525827 prefixEnd_2525827 := by exact prefixLift 2525827
  have htrace : WordTrace (prefixWord ++ tailWord_2525827) baseStart_2525827 baseEnd_2525827 := by
    simpa [prefixWord, tailWord_2525827, baseEnd_2525827] using wordTrace_append hprefix tailTrace_2525827
  have hstable : (prefixWord ++ tailWord_2525827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525827).length < 2 ^ (prefixWord ++ tailWord_2525827).sum := by decide
  have hdescent : baseEnd_2525827 < baseStart_2525827 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525884 : List Nat := [2, 2, 2, 3, 1, 1, 1, 4, 1, 4, 2]
def baseStart_2525884 : Nat := 118140960795 + 2525884 * 2 ^ 59
def prefixEnd_2525884 : Nat := 4983230072969 + 3 ^ 40 * 2525884 * 2
def baseEnd_2525884 : Nat := 1296992569501300700933677

theorem tailTrace_2525884 : CollatzResearch.WordTrace tailWord_2525884 prefixEnd_2525884 1296992569501300700933677 := by
  unfold tailWord_2525884
  simp only [CollatzResearch.WordTrace]
  refine ⟨46063278990580564743932353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61417705320774086325243137 46063278990580564743932353)
  ·
    refine ⟨34547459242935423557949265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46063278990580564743932353 34547459242935423557949265)
    ·
      refine ⟨25910594432201567668461949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34547459242935423557949265 25910594432201567668461949)
      ·
        refine ⟨9716472912075587875673231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25910594432201567668461949 9716472912075587875673231)
        ·
          refine ⟨14574709368113381813509847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9716472912075587875673231 14574709368113381813509847)
          ·
            refine ⟨21862064052170072720264771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14574709368113381813509847 21862064052170072720264771)
            ·
              refine ⟨32793096078255109080397157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21862064052170072720264771 32793096078255109080397157)
              ·
                refine ⟨6148705514672832952574467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32793096078255109080397157 6148705514672832952574467)
                ·
                  refine ⟨9223058272009249428861701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6148705514672832952574467 9223058272009249428861701)
                  ·
                    refine ⟨1729323426001734267911569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9223058272009249428861701 1729323426001734267911569)
                    ·
                      refine ⟨1296992569501300700933677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1729323426001734267911569 1296992569501300700933677)
                      ·
                        rfl

theorem cell23_2525884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_2525884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2525884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2525884 prefixEnd_2525884 := by exact prefixLift 2525884
  have htrace : WordTrace (prefixWord ++ tailWord_2525884) baseStart_2525884 baseEnd_2525884 := by
    simpa [prefixWord, tailWord_2525884, baseEnd_2525884] using wordTrace_append hprefix tailTrace_2525884
  have hstable : (prefixWord ++ tailWord_2525884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525884).length < 2 ^ (prefixWord ++ tailWord_2525884).sum := by decide
  have hdescent : baseEnd_2525884 < baseStart_2525884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525888 : List Nat := [2, 1, 1, 2, 4, 4, 2, 1, 1, 3, 2]
def baseStart_2525888 : Nat := 118140960795 + 2525888 * 2 ^ 59
def prefixEnd_2525888 : Nat := 4983230072969 + 3 ^ 40 * 2525888 * 2
def baseEnd_2525888 : Nat := 1296994623423918685283659

theorem tailTrace_2525888 : CollatzResearch.WordTrace tailWord_2525888 prefixEnd_2525888 1296994623423918685283659 := by
  unfold tailWord_2525888
  simp only [CollatzResearch.WordTrace]
  refine ⟨46063351936573319085505159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61417802582097758780673545 46063351936573319085505159)
  ·
    refine ⟨69095027904859978628257739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46063351936573319085505159 69095027904859978628257739)
    ·
      refine ⟨103642541857289967942386609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69095027904859978628257739 103642541857289967942386609)
      ·
        refine ⟨77731906392967475956789957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103642541857289967942386609 77731906392967475956789957)
        ·
          refine ⟨14574732448681401741898117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77731906392967475956789957 14574732448681401741898117)
          ·
            refine ⟨2732762334127762826605897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14574732448681401741898117 2732762334127762826605897)
            ·
              refine ⟨2049571750595822119954423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2732762334127762826605897 2049571750595822119954423)
              ·
                refine ⟨3074357625893733179931635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2049571750595822119954423 3074357625893733179931635)
                ·
                  refine ⟨4611536438840599769897453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3074357625893733179931635 4611536438840599769897453)
                  ·
                    refine ⟨1729326164565224913711545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4611536438840599769897453 1729326164565224913711545)
                    ·
                      refine ⟨1296994623423918685283659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1729326164565224913711545 1296994623423918685283659)
                      ·
                        rfl

theorem cell23_2525888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2, 1, 1, 3, 2].length) (baseStart_2525888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2525888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2525888 prefixEnd_2525888 := by exact prefixLift 2525888
  have htrace : WordTrace (prefixWord ++ tailWord_2525888) baseStart_2525888 baseEnd_2525888 := by
    simpa [prefixWord, tailWord_2525888, baseEnd_2525888] using wordTrace_append hprefix tailTrace_2525888
  have hstable : (prefixWord ++ tailWord_2525888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525888).length < 2 ^ (prefixWord ++ tailWord_2525888).sum := by decide
  have hdescent : baseEnd_2525888 < baseStart_2525888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525937 : List Nat := [1, 2, 2, 2, 2, 2, 2, 3, 2, 5]
def baseStart_2525937 : Nat := 118140960795 + 2525937 * 2 ^ 59
def prefixEnd_2525937 : Nat := 4983230072969 + 3 ^ 40 * 2525937 * 2
def baseEnd_2525937 : Nat := 432339927991996331190311

theorem tailTrace_2525937 : CollatzResearch.WordTrace tailWord_2525937 prefixEnd_2525937 432339927991996331190311 := by
  unfold tailWord_2525937
  simp only [CollatzResearch.WordTrace]
  refine ⟨92128491049969119539544065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61418994033312746359696043 92128491049969119539544065)
  ·
    refine ⟨69096368287476839654658049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92128491049969119539544065 69096368287476839654658049)
    ·
      refine ⟨51822276215607629740993537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69096368287476839654658049 51822276215607629740993537)
      ·
        refine ⟨38866707161705722305745153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51822276215607629740993537 38866707161705722305745153)
        ·
          refine ⟨29150030371279291729308865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38866707161705722305745153 29150030371279291729308865)
          ·
            refine ⟨21862522778459468796981649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29150030371279291729308865 21862522778459468796981649)
            ·
              refine ⟨16396892083844601597736237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21862522778459468796981649 16396892083844601597736237)
              ·
                refine ⟨6148834531441725599151089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16396892083844601597736237 6148834531441725599151089)
                ·
                  refine ⟨4611625898581294199363317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6148834531441725599151089 4611625898581294199363317)
                  ·
                    refine ⟨432339927991996331190311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4611625898581294199363317 432339927991996331190311)
                    ·
                      rfl

theorem cell23_2525937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 2, 5].length) (baseStart_2525937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2525937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2525937 prefixEnd_2525937 := by exact prefixLift 2525937
  have htrace : WordTrace (prefixWord ++ tailWord_2525937) baseStart_2525937 baseEnd_2525937 := by
    simpa [prefixWord, tailWord_2525937, baseEnd_2525937] using wordTrace_append hprefix tailTrace_2525937
  have hstable : (prefixWord ++ tailWord_2525937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525937).length < 2 ^ (prefixWord ++ tailWord_2525937).sum := by decide
  have hdescent : baseEnd_2525937 < baseStart_2525937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525954 : List Nat := [3, 4, 1, 1, 1, 2, 1, 1, 4, 5]
def baseStart_2525954 : Nat := 118140960795 + 2525954 * 2 ^ 59
def prefixEnd_2525954 : Nat := 4983230072969 + 3 ^ 40 * 2525954 * 2
def baseEnd_2525954 : Nat := 432342837715705142352785

theorem tailTrace_2525954 : CollatzResearch.WordTrace tailWord_2525954 prefixEnd_2525954 432342837715705142352785 := by
  unfold tailWord_2525954
  simp only [CollatzResearch.WordTrace]
  refine ⟨23032277772726882860728229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61419407393938354295275277 23032277772726882860728229)
  ·
    refine ⟨4318552082386290536386543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23032277772726882860728229 4318552082386290536386543)
    ·
      refine ⟨6477828123579435804579815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4318552082386290536386543 6477828123579435804579815)
      ·
        refine ⟨9716742185369153706869723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6477828123579435804579815 9716742185369153706869723)
        ·
          refine ⟨14575113278053730560304585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9716742185369153706869723 14575113278053730560304585)
          ·
            refine ⟨10931334958540297920228439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14575113278053730560304585 10931334958540297920228439)
            ·
              refine ⟨16397002437810446880342659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10931334958540297920228439 16397002437810446880342659)
              ·
                refine ⟨24595503656715670320513989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16397002437810446880342659 24595503656715670320513989)
                ·
                  refine ⟨4611656935634188185096373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24595503656715670320513989 4611656935634188185096373)
                  ·
                    refine ⟨432342837715705142352785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4611656935634188185096373 432342837715705142352785)
                    ·
                      rfl

theorem cell23_2525954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_2525954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2525954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2525954 prefixEnd_2525954 := by exact prefixLift 2525954
  have htrace : WordTrace (prefixWord ++ tailWord_2525954) baseStart_2525954 baseEnd_2525954 := by
    simpa [prefixWord, tailWord_2525954, baseEnd_2525954] using wordTrace_append hprefix tailTrace_2525954
  have hstable : (prefixWord ++ tailWord_2525954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525954).length < 2 ^ (prefixWord ++ tailWord_2525954).sum := by decide
  have hdescent : baseEnd_2525954 < baseStart_2525954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525977 : List Nat := [1, 2, 1, 2, 1, 1, 1, 6, 1, 4, 3]
def baseStart_2525977 : Nat := 118140960795 + 2525977 * 2 ^ 59
def prefixEnd_2525977 : Nat := 4983230072969 + 3 ^ 40 * 2525977 * 2
def baseEnd_2525977 : Nat := 1297040323202168837070749

theorem tailTrace_2525977 : CollatzResearch.WordTrace tailWord_2525977 prefixEnd_2525977 1297040323202168837070749 := by
  unfold tailWord_2525977
  simp only [CollatzResearch.WordTrace]
  refine ⟨92129949969824206371000185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61419966646549470914000123 92129949969824206371000185)
  ·
    refine ⟨69097462477368154778250139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92129949969824206371000185 69097462477368154778250139)
    ·
      refine ⟨103646193716052232167375209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69097462477368154778250139 103646193716052232167375209)
      ·
        refine ⟨77734645287039174125531407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103646193716052232167375209 77734645287039174125531407)
        ·
          refine ⟨116601967930558761188297111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77734645287039174125531407 116601967930558761188297111)
          ·
            refine ⟨174902951895838141782445667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116601967930558761188297111 174902951895838141782445667)
            ·
              refine ⟨262354427843757212673668501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174902951895838141782445667 262354427843757212673668501)
              ·
                refine ⟨12297863805176119344078211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 262354427843757212673668501 12297863805176119344078211)
                ·
                  refine ⟨18446795707764179016117317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12297863805176119344078211 18446795707764179016117317)
                  ·
                    refine ⟨3458774195205783565521997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18446795707764179016117317 3458774195205783565521997)
                    ·
                      refine ⟨1297040323202168837070749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3458774195205783565521997 1297040323202168837070749)
                      ·
                        rfl

theorem cell23_2525977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 4, 3].length) (baseStart_2525977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2525977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2525977 prefixEnd_2525977 := by exact prefixLift 2525977
  have htrace : WordTrace (prefixWord ++ tailWord_2525977) baseStart_2525977 baseEnd_2525977 := by
    simpa [prefixWord, tailWord_2525977, baseEnd_2525977] using wordTrace_append hprefix tailTrace_2525977
  have hstable : (prefixWord ++ tailWord_2525977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525977).length < 2 ^ (prefixWord ++ tailWord_2525977).sum := by decide
  have hdescent : baseEnd_2525977 < baseStart_2525977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526001 : List Nat := [1, 2, 2, 3, 2, 1, 2, 5, 1, 4]
def baseStart_2526001 : Nat := 118140960795 + 2526001 * 2 ^ 59
def prefixEnd_2526001 : Nat := 4983230072969 + 3 ^ 40 * 2526001 * 2
def baseEnd_2526001 : Nat := 432350882245958914390213

theorem tailTrace_2526001 : CollatzResearch.WordTrace tailWord_2526001 prefixEnd_2526001 432350882245958914390213 := by
  unfold tailWord_2526001
  simp only [CollatzResearch.WordTrace]
  refine ⟨92130825321737258469873857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61420550214491505646582571 92130825321737258469873857)
  ·
    refine ⟨69098118991302943852405393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92130825321737258469873857 69098118991302943852405393)
    ·
      refine ⟨51823589243477207889304045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69098118991302943852405393 51823589243477207889304045)
      ·
        refine ⟨19433845966303952958489017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51823589243477207889304045 19433845966303952958489017)
        ·
          refine ⟨14575384474727964718866763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19433845966303952958489017 14575384474727964718866763)
          ·
            refine ⟨21863076712091947078300145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14575384474727964718866763 21863076712091947078300145)
            ·
              refine ⟨16397307534068960308725109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21863076712091947078300145 16397307534068960308725109)
              ·
                refine ⟨1537247581318965028942979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16397307534068960308725109 1537247581318965028942979)
                ·
                  refine ⟨2305871371978447543414469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1537247581318965028942979 2305871371978447543414469)
                  ·
                    refine ⟨432350882245958914390213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2305871371978447543414469 432350882245958914390213)
                    ·
                      rfl

theorem cell23_2526001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 5, 1, 4].length) (baseStart_2526001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2526001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2526001 prefixEnd_2526001 := by exact prefixLift 2526001
  have htrace : WordTrace (prefixWord ++ tailWord_2526001) baseStart_2526001 baseEnd_2526001 := by
    simpa [prefixWord, tailWord_2526001, baseEnd_2526001] using wordTrace_append hprefix tailTrace_2526001
  have hstable : (prefixWord ++ tailWord_2526001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526001).length < 2 ^ (prefixWord ++ tailWord_2526001).sum := by decide
  have hdescent : baseEnd_2526001 < baseStart_2526001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526037 : List Nat := [1, 3, 2, 2, 2, 1, 1, 1, 2, 1, 7]
def baseStart_2526037 : Nat := 118140960795 + 2526037 * 2 ^ 59
def prefixEnd_2526037 : Nat := 4983230072969 + 3 ^ 40 * 2526037 * 2
def baseEnd_2526037 : Nat := 1297071132041438602320473

theorem tailTrace_2526037 : CollatzResearch.WordTrace tailWord_2526037 prefixEnd_2526037 1297071132041438602320473 := by
  unfold tailWord_2526037
  simp only [CollatzResearch.WordTrace]
  refine ⟨92132138349606836618184365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61421425566404557745456243 92132138349606836618184365)
  ·
    refine ⟨34549551881102563731819137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92132138349606836618184365 34549551881102563731819137)
    ·
      refine ⟨25912163910826922798864353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34549551881102563731819137 25912163910826922798864353)
      ·
        refine ⟨19434122933120192099148265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25912163910826922798864353 19434122933120192099148265)
        ·
          refine ⟨14575592199840144074361199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19434122933120192099148265 14575592199840144074361199)
          ·
            refine ⟨21863388299760216111541799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14575592199840144074361199 21863388299760216111541799)
            ·
              refine ⟨32795082449640324167312699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21863388299760216111541799 32795082449640324167312699)
              ·
                refine ⟨49192623674460486250969049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32795082449640324167312699 49192623674460486250969049)
                ·
                  refine ⟨36894467755845364688226787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49192623674460486250969049 36894467755845364688226787)
                  ·
                    refine ⟨55341701633768047032340181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36894467755845364688226787 55341701633768047032340181)
                    ·
                      refine ⟨1297071132041438602320473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 55341701633768047032340181 1297071132041438602320473)
                      ·
                        rfl

theorem cell23_2526037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_2526037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2526037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2526037 prefixEnd_2526037 := by exact prefixLift 2526037
  have htrace : WordTrace (prefixWord ++ tailWord_2526037) baseStart_2526037 baseEnd_2526037 := by
    simpa [prefixWord, tailWord_2526037, baseEnd_2526037] using wordTrace_append hprefix tailTrace_2526037
  have hstable : (prefixWord ++ tailWord_2526037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526037).length < 2 ^ (prefixWord ++ tailWord_2526037).sum := by decide
  have hdescent : baseEnd_2526037 < baseStart_2526037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526041 : List Nat := [1, 2, 1, 2, 2, 5, 1, 2, 3, 1, 3]
def baseStart_2526041 : Nat := 118140960795 + 2526041 * 2 ^ 59
def prefixEnd_2526041 : Nat := 4983230072969 + 3 ^ 40 * 2526041 * 2
def baseEnd_2526041 : Nat := 1297073185964056586670455

theorem tailTrace_2526041 : CollatzResearch.WordTrace tailWord_2526041 prefixEnd_2526041 1297073185964056586670455 := by
  unfold tailWord_2526041
  simp only [CollatzResearch.WordTrace]
  refine ⟨92132284241592345301329977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61421522827728230200886651 92132284241592345301329977)
  ·
    refine ⟨69099213181194258975997483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92132284241592345301329977 69099213181194258975997483)
    ·
      refine ⟨103648819771791388463996225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69099213181194258975997483 103648819771791388463996225)
      ·
        refine ⟨77736614828843541347997169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103648819771791388463996225 77736614828843541347997169)
        ·
          refine ⟨58302461121632656010997877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77736614828843541347997169 58302461121632656010997877)
          ·
            refine ⟨5465855730153061501031051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58302461121632656010997877 5465855730153061501031051)
            ·
              refine ⟨8198783595229592251546577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5465855730153061501031051 8198783595229592251546577)
              ·
                refine ⟨6149087696422194188659933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8198783595229592251546577 6149087696422194188659933)
                ·
                  refine ⟨2305907886158322820747475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6149087696422194188659933 2305907886158322820747475)
                  ·
                    refine ⟨3458861829237484231121213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2305907886158322820747475 3458861829237484231121213)
                    ·
                      refine ⟨1297073185964056586670455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3458861829237484231121213 1297073185964056586670455)
                      ·
                        rfl

theorem cell23_2526041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 2, 3, 1, 3].length) (baseStart_2526041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2526041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2526041 prefixEnd_2526041 := by exact prefixLift 2526041
  have htrace : WordTrace (prefixWord ++ tailWord_2526041) baseStart_2526041 baseEnd_2526041 := by
    simpa [prefixWord, tailWord_2526041, baseEnd_2526041] using wordTrace_append hprefix tailTrace_2526041
  have hstable : (prefixWord ++ tailWord_2526041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526041).length < 2 ^ (prefixWord ++ tailWord_2526041).sum := by decide
  have hdescent : baseEnd_2526041 < baseStart_2526041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526051 : List Nat := [1, 1, 1, 5, 3, 2, 1, 1, 1, 5, 2]
def baseStart_2526051 : Nat := 118140960795 + 2526051 * 2 ^ 59
def prefixEnd_2526051 : Nat := 4983230072969 + 3 ^ 40 * 2526051 * 2
def baseEnd_2526051 : Nat := 1297078320770601547545409

theorem tailTrace_2526051 : CollatzResearch.WordTrace tailWord_2526051 prefixEnd_2526051 1297078320770601547545409 := by
  unfold tailWord_2526051
  simp only [CollatzResearch.WordTrace]
  refine ⟨92132648971556117009194007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61421765981037411339462671 92132648971556117009194007)
  ·
    refine ⟨138198973457334175513791011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92132648971556117009194007 138198973457334175513791011)
    ·
      refine ⟨207298460186001263270686517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138198973457334175513791011 207298460186001263270686517)
      ·
        refine ⟨19434230642437618431626861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 207298460186001263270686517 19434230642437618431626861)
        ·
          refine ⟨7287836490914106911860073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19434230642437618431626861 7287836490914106911860073)
          ·
            refine ⟨5465877368185580183895055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7287836490914106911860073 5465877368185580183895055)
            ·
              refine ⟨8198816052278370275842583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5465877368185580183895055 8198816052278370275842583)
              ·
                refine ⟨12298224078417555413763875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8198816052278370275842583 12298224078417555413763875)
                ·
                  refine ⟨18447336117626333120645813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12298224078417555413763875 18447336117626333120645813)
                  ·
                    refine ⟨1729437761027468730060545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18447336117626333120645813 1729437761027468730060545)
                    ·
                      refine ⟨1297078320770601547545409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1729437761027468730060545 1297078320770601547545409)
                      ·
                        rfl

theorem cell23_2526051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 5, 2].length) (baseStart_2526051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2526051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2526051 prefixEnd_2526051 := by exact prefixLift 2526051
  have htrace : WordTrace (prefixWord ++ tailWord_2526051) baseStart_2526051 baseEnd_2526051 := by
    simpa [prefixWord, tailWord_2526051, baseEnd_2526051] using wordTrace_append hprefix tailTrace_2526051
  have hstable : (prefixWord ++ tailWord_2526051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526051).length < 2 ^ (prefixWord ++ tailWord_2526051).sum := by decide
  have hdescent : baseEnd_2526051 < baseStart_2526051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526101 : List Nat := [1, 3, 2, 1, 1, 4, 1, 4, 1, 2, 3]
def baseStart_2526101 : Nat := 118140960795 + 2526101 * 2 ^ 59
def prefixEnd_2526101 : Nat := 4983230072969 + 3 ^ 40 * 2526101 * 2
def baseEnd_2526101 : Nat := 1297103994803326351920179

theorem tailTrace_2526101 : CollatzResearch.WordTrace tailWord_2526101 prefixEnd_2526101 1297103994803326351920179 := by
  unfold tailWord_2526101
  simp only [CollatzResearch.WordTrace]
  refine ⟨92134472621374975548514157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61422981747583317032342771 92134472621374975548514157)
  ·
    refine ⟨34550427233015615830692809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92134472621374975548514157 34550427233015615830692809)
    ·
      refine ⟨25912820424761711873019607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34550427233015615830692809 25912820424761711873019607)
      ·
        refine ⟨38869230637142567809529411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25912820424761711873019607 38869230637142567809529411)
        ·
          refine ⟨58303845955713851714294117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38869230637142567809529411 58303845955713851714294117)
          ·
            refine ⟨10931971116696347196430147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58303845955713851714294117 10931971116696347196430147)
            ·
              refine ⟨16397956675044520794645221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10931971116696347196430147 16397956675044520794645221)
              ·
                refine ⟨3074616876570847648995979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16397956675044520794645221 3074616876570847648995979)
                ·
                  refine ⟨4611925314856271473493969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3074616876570847648995979 4611925314856271473493969)
                  ·
                    refine ⟨3458943986142203605120477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4611925314856271473493969 3458943986142203605120477)
                    ·
                      refine ⟨1297103994803326351920179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3458943986142203605120477 1297103994803326351920179)
                      ·
                        rfl

theorem cell23_2526101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 4, 1, 2, 3].length) (baseStart_2526101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2526101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2526101 prefixEnd_2526101 := by exact prefixLift 2526101
  have htrace : WordTrace (prefixWord ++ tailWord_2526101) baseStart_2526101 baseEnd_2526101 := by
    simpa [prefixWord, tailWord_2526101, baseEnd_2526101] using wordTrace_append hprefix tailTrace_2526101
  have hstable : (prefixWord ++ tailWord_2526101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526101).length < 2 ^ (prefixWord ++ tailWord_2526101).sum := by decide
  have hdescent : baseEnd_2526101 < baseStart_2526101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526115 : List Nat := [1, 1, 1, 4, 1, 2, 5, 3, 1, 2, 2]
def baseStart_2526115 : Nat := 118140960795 + 2526115 * 2 ^ 59
def prefixEnd_2526115 : Nat := 4983230072969 + 3 ^ 40 * 2526115 * 2
def baseEnd_2526115 : Nat := 1297111183532489297145115

theorem tailTrace_2526115 : CollatzResearch.WordTrace tailWord_2526115 prefixEnd_2526115 1297111183532489297145115 := by
  unfold tailWord_2526115
  simp only [CollatzResearch.WordTrace]
  refine ⟨92134983243324255939523799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61423322162216170626349199 92134983243324255939523799)
  ·
    refine ⟨138202474864986383909285699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92134983243324255939523799 138202474864986383909285699)
    ·
      refine ⟨207303712297479575863928549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138202474864986383909285699 207303712297479575863928549)
      ·
        refine ⟨38869446055777420474486603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 207303712297479575863928549 38869446055777420474486603)
        ·
          refine ⟨58304169083666130711729905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38869446055777420474486603 58304169083666130711729905)
          ·
            refine ⟨43728126812749598033797429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58304169083666130711729905 43728126812749598033797429)
            ·
              refine ⟨4099511888695274815668509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43728126812749598033797429 4099511888695274815668509)
              ·
                refine ⟨1537316958260728055875691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4099511888695274815668509 1537316958260728055875691)
                ·
                  refine ⟨2305975437391092083813537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1537316958260728055875691 2305975437391092083813537)
                  ·
                    refine ⟨1729481578043319062860153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2305975437391092083813537 1729481578043319062860153)
                    ·
                      refine ⟨1297111183532489297145115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1729481578043319062860153 1297111183532489297145115)
                      ·
                        rfl

theorem cell23_2526115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 3, 1, 2, 2].length) (baseStart_2526115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2526115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2526115 prefixEnd_2526115 := by exact prefixLift 2526115
  have htrace : WordTrace (prefixWord ++ tailWord_2526115) baseStart_2526115 baseEnd_2526115 := by
    simpa [prefixWord, tailWord_2526115, baseEnd_2526115] using wordTrace_append hprefix tailTrace_2526115
  have hstable : (prefixWord ++ tailWord_2526115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526115).length < 2 ^ (prefixWord ++ tailWord_2526115).sum := by decide
  have hdescent : baseEnd_2526115 < baseStart_2526115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526117 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 3, 9]
def baseStart_2526117 : Nat := 118140960795 + 2526117 * 2 ^ 59
def prefixEnd_2526117 : Nat := 4983230072969 + 3 ^ 40 * 2526117 * 2
def baseEnd_2526117 : Nat := 432370736831266096440035

theorem tailTrace_2526117 : CollatzResearch.WordTrace tailWord_2526117 prefixEnd_2526117 432370736831266096440035 := by
  unfold tailWord_2526117
  simp only [CollatzResearch.WordTrace]
  refine ⟨92135056189317010281096605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61423370792878006854064403 92135056189317010281096605)
  ·
    refine ⟨34550646070993878855411227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92135056189317010281096605 34550646070993878855411227)
    ·
      refine ⟨51825969106490818283116841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34550646070993878855411227 51825969106490818283116841)
      ·
        refine ⟨38869476829868113712337631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51825969106490818283116841 38869476829868113712337631)
        ·
          refine ⟨58304215244802170568506447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38869476829868113712337631 58304215244802170568506447)
          ·
            refine ⟨87456322867203255852759671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58304215244802170568506447 87456322867203255852759671)
            ·
              refine ⟨131184484300804883779139507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87456322867203255852759671 131184484300804883779139507)
              ·
                refine ⟨196776726451207325668709261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131184484300804883779139507 196776726451207325668709261)
                ·
                  refine ⟨73791272419202747125765973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 196776726451207325668709261 73791272419202747125765973)
                  ·
                    refine ⟨432370736831266096440035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 73791272419202747125765973 432370736831266096440035)
                    ·
                      rfl

theorem cell23_2526117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 9].length) (baseStart_2526117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2526117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2526117 prefixEnd_2526117 := by exact prefixLift 2526117
  have htrace : WordTrace (prefixWord ++ tailWord_2526117) baseStart_2526117 baseEnd_2526117 := by
    simpa [prefixWord, tailWord_2526117, baseEnd_2526117] using wordTrace_append hprefix tailTrace_2526117
  have hstable : (prefixWord ++ tailWord_2526117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526117).length < 2 ^ (prefixWord ++ tailWord_2526117).sum := by decide
  have hdescent : baseEnd_2526117 < baseStart_2526117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526132 : List Nat := [2, 5, 2, 1, 1, 1, 3, 1, 3, 2, 2]
def baseStart_2526132 : Nat := 118140960795 + 2526132 * 2 ^ 59
def prefixEnd_2526132 : Nat := 4983230072969 + 3 ^ 40 * 2526132 * 2
def baseEnd_2526132 : Nat := 1297119912703615730632537

theorem tailTrace_2526132 : CollatzResearch.WordTrace tailWord_2526132 prefixEnd_2526132 1297119912703615730632537 := by
  unfold tailWord_2526132
  simp only [CollatzResearch.WordTrace]
  refine ⟨46067801642131333921446325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61423735522841778561928433 46067801642131333921446325)
  ·
    refine ⟨4318856403949812555135593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46067801642131333921446325 4318856403949812555135593)
    ·
      refine ⟨3239142302962359416351695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4318856403949812555135593 3239142302962359416351695)
      ·
        refine ⟨4858713454443539124527543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3239142302962359416351695 4858713454443539124527543)
        ·
          refine ⟨7288070181665308686791315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4858713454443539124527543 7288070181665308686791315)
          ·
            refine ⟨10932105272497963030186973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7288070181665308686791315 10932105272497963030186973)
            ·
              refine ⟨4099539477186736136320115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10932105272497963030186973 4099539477186736136320115)
              ·
                refine ⟨6149309215780104204480173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4099539477186736136320115 6149309215780104204480173)
                ·
                  refine ⟨2305990955917539076680065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6149309215780104204480173 2305990955917539076680065)
                  ·
                    refine ⟨1729493216938154307510049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2305990955917539076680065 1729493216938154307510049)
                    ·
                      refine ⟨1297119912703615730632537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1729493216938154307510049 1297119912703615730632537)
                      ·
                        rfl

theorem cell23_2526132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_2526132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2526132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2526132 prefixEnd_2526132 := by exact prefixLift 2526132
  have htrace : WordTrace (prefixWord ++ tailWord_2526132) baseStart_2526132 baseEnd_2526132 := by
    simpa [prefixWord, tailWord_2526132, baseEnd_2526132] using wordTrace_append hprefix tailTrace_2526132
  have hstable : (prefixWord ++ tailWord_2526132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526132).length < 2 ^ (prefixWord ++ tailWord_2526132).sum := by decide
  have hdescent : baseEnd_2526132 < baseStart_2526132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526158 : List Nat := [4, 1, 1, 1, 2, 4, 1, 1, 3, 3, 2]
def baseStart_2526158 : Nat := 118140960795 + 2526158 * 2 ^ 59
def prefixEnd_2526158 : Nat := 4983230072969 + 3 ^ 40 * 2526158 * 2
def baseEnd_2526158 : Nat := 1297133263200632628907417

theorem tailTrace_2526158 : CollatzResearch.WordTrace tailWord_2526158 prefixEnd_2526158 1297133263200632628907417 := by
  unfold tailWord_2526158
  simp only [CollatzResearch.WordTrace]
  refine ⟨11517068947771059285417391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61424367721445649522226085 11517068947771059285417391)
  ·
    refine ⟨17275603421656588928126087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11517068947771059285417391 17275603421656588928126087)
    ·
      refine ⟨25913405132484883392189131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17275603421656588928126087 25913405132484883392189131)
      ·
        refine ⟨38870107698727325088283697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25913405132484883392189131 38870107698727325088283697)
        ·
          refine ⟨29152580774045493816212773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38870107698727325088283697 29152580774045493816212773)
          ·
            refine ⟨5466108895133530090539895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29152580774045493816212773 5466108895133530090539895)
            ·
              refine ⟨8199163342700295135809843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5466108895133530090539895 8199163342700295135809843)
              ·
                refine ⟨12298745014050442703714765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8199163342700295135809843 12298745014050442703714765)
                ·
                  refine ⟨4612029380268916013893037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12298745014050442703714765 4612029380268916013893037)
                  ·
                    refine ⟨1729511017600843505209889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4612029380268916013893037 1729511017600843505209889)
                    ·
                      refine ⟨1297133263200632628907417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1729511017600843505209889 1297133263200632628907417)
                      ·
                        rfl

theorem cell23_2526158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 3, 3, 2].length) (baseStart_2526158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2526158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2526158 prefixEnd_2526158 := by exact prefixLift 2526158
  have htrace : WordTrace (prefixWord ++ tailWord_2526158) baseStart_2526158 baseEnd_2526158 := by
    simpa [prefixWord, tailWord_2526158, baseEnd_2526158] using wordTrace_append hprefix tailTrace_2526158
  have hstable : (prefixWord ++ tailWord_2526158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526158).length < 2 ^ (prefixWord ++ tailWord_2526158).sum := by decide
  have hdescent : baseEnd_2526158 < baseStart_2526158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526318 : List Nat := [4, 1, 2, 2, 1, 3, 1, 3, 6]
def baseStart_2526318 : Nat := 118140960795 + 2526318 * 2 ^ 59
def prefixEnd_2526318 : Nat := 4983230072969 + 3 ^ 40 * 2526318 * 2
def baseEnd_2526318 : Nat := 144135046678372444767409

theorem tailTrace_2526318 : CollatzResearch.WordTrace tailWord_2526318 prefixEnd_2526318 144135046678372444767409 := by
  unfold tailWord_2526318
  simp only [CollatzResearch.WordTrace]
  refine ⟨11517798407698602701145451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61428258174392547739442405 11517798407698602701145451)
  ·
    refine ⟨17276697611547904051718177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11517798407698602701145451 17276697611547904051718177)
    ·
      refine ⟨12957523208660928038788633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17276697611547904051718177 12957523208660928038788633)
      ·
        refine ⟨9718142406495696029091475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12957523208660928038788633 9718142406495696029091475)
        ·
          refine ⟨14577213609743544043637213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9718142406495696029091475 14577213609743544043637213)
          ·
            refine ⟨5466455103653829016363955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14577213609743544043637213 5466455103653829016363955)
            ·
              refine ⟨8199682655480743524545933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5466455103653829016363955 8199682655480743524545933)
              ·
                refine ⟨3074880995805278821704725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8199682655480743524545933 3074880995805278821704725)
                ·
                  refine ⟨144135046678372444767409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3074880995805278821704725 144135046678372444767409)
                  ·
                    rfl

theorem cell23_2526318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 3, 6].length) (baseStart_2526318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2526318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2526318 prefixEnd_2526318 := by exact prefixLift 2526318
  have htrace : WordTrace (prefixWord ++ tailWord_2526318) baseStart_2526318 baseEnd_2526318 := by
    simpa [prefixWord, tailWord_2526318, baseEnd_2526318] using wordTrace_append hprefix tailTrace_2526318
  have hstable : (prefixWord ++ tailWord_2526318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526318).length < 2 ^ (prefixWord ++ tailWord_2526318).sum := by decide
  have hdescent : baseEnd_2526318 < baseStart_2526318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526328 : List Nat := [2, 1, 2, 1, 1, 1, 4, 4, 3, 1, 3]
def baseStart_2526328 : Nat := 118140960795 + 2526328 * 2 ^ 59
def prefixEnd_2526328 : Nat := 4983230072969 + 3 ^ 40 * 2526328 * 2
def baseEnd_2526328 : Nat := 1297220554911896963781635

theorem tailTrace_2526328 : CollatzResearch.WordTrace tailWord_2526328 prefixEnd_2526328 1297220554911896963781635 := by
  unfold tailWord_2526328
  simp only [CollatzResearch.WordTrace]
  refine ⟨46071375995776296658513819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61428501327701728878018425 46071375995776296658513819)
  ·
    refine ⟨69107063993664444987770729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46071375995776296658513819 69107063993664444987770729)
    ·
      refine ⟨51830297995248333740828047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69107063993664444987770729 51830297995248333740828047)
      ·
        refine ⟨77745446992872500611242071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51830297995248333740828047 77745446992872500611242071)
        ·
          refine ⟨116618170489308750916863107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77745446992872500611242071 116618170489308750916863107)
          ·
            refine ⟨174927255733963126375294661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116618170489308750916863107 174927255733963126375294661)
            ·
              refine ⟨32798860450118086195367749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 174927255733963126375294661 32798860450118086195367749)
              ·
                refine ⟨6149786334397141161631453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32798860450118086195367749 6149786334397141161631453)
                ·
                  refine ⟨2306169875398927935611795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6149786334397141161631453 2306169875398927935611795)
                  ·
                    refine ⟨3459254813098391903417693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2306169875398927935611795 3459254813098391903417693)
                    ·
                      refine ⟨1297220554911896963781635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3459254813098391903417693 1297220554911896963781635)
                      ·
                        rfl

theorem cell23_2526328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4, 3, 1, 3].length) (baseStart_2526328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2526328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2526328 prefixEnd_2526328 := by exact prefixLift 2526328
  have htrace : WordTrace (prefixWord ++ tailWord_2526328) baseStart_2526328 baseEnd_2526328 := by
    simpa [prefixWord, tailWord_2526328, baseEnd_2526328] using wordTrace_append hprefix tailTrace_2526328
  have hstable : (prefixWord ++ tailWord_2526328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526328).length < 2 ^ (prefixWord ++ tailWord_2526328).sum := by decide
  have hdescent : baseEnd_2526328 < baseStart_2526328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526371 : List Nat := [1, 1, 1, 4, 1, 1, 1, 6, 1, 1, 5]
def baseStart_2526371 : Nat := 118140960795 + 2526371 * 2 ^ 59
def prefixEnd_2526371 : Nat := 4983230072969 + 3 ^ 40 * 2526371 * 2
def baseEnd_2526371 : Nat := 1297242634580040295543937

theorem tailTrace_2526371 : CollatzResearch.WordTrace tailWord_2526371 prefixEnd_2526371 1297242634580040295543937 := by
  unfold tailWord_2526371
  simp only [CollatzResearch.WordTrace]
  refine ⟨92144320330396811660842967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61429546886931207773895311 92144320330396811660842967)
  ·
    refine ⟨138216480495595217491264451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92144320330396811660842967 138216480495595217491264451)
    ·
      refine ⟨207324720743392826236896677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138216480495595217491264451 207324720743392826236896677)
      ·
        refine ⟨38873385139386154919418127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 207324720743392826236896677 38873385139386154919418127)
        ·
          refine ⟨58310077709079232379127191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38873385139386154919418127 58310077709079232379127191)
          ·
            refine ⟨87465116563618848568690787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58310077709079232379127191 87465116563618848568690787)
            ·
              refine ⟨131197674845428272853036181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87465116563618848568690787 131197674845428272853036181)
              ·
                refine ⟨6149891008379450289986071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 131197674845428272853036181 6149891008379450289986071)
                ·
                  refine ⟨9224836512569175434979107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6149891008379450289986071 9224836512569175434979107)
                  ·
                    refine ⟨13837254768853763152468661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9224836512569175434979107 13837254768853763152468661)
                    ·
                      refine ⟨1297242634580040295543937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13837254768853763152468661 1297242634580040295543937)
                      ·
                        rfl

theorem cell23_2526371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6, 1, 1, 5].length) (baseStart_2526371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2526371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2526371 prefixEnd_2526371 := by exact prefixLift 2526371
  have htrace : WordTrace (prefixWord ++ tailWord_2526371) baseStart_2526371 baseEnd_2526371 := by
    simpa [prefixWord, tailWord_2526371, baseEnd_2526371] using wordTrace_append hprefix tailTrace_2526371
  have hstable : (prefixWord ++ tailWord_2526371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526371).length < 2 ^ (prefixWord ++ tailWord_2526371).sum := by decide
  have hdescent : baseEnd_2526371 < baseStart_2526371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526422 : List Nat := [5, 2, 1, 2, 2, 1, 1, 2, 1, 1, 5]
def baseStart_2526422 : Nat := 118140960795 + 2526422 * 2 ^ 59
def prefixEnd_2526422 : Nat := 4983230072969 + 3 ^ 40 * 2526422 * 2
def baseEnd_2526422 : Nat := 1297268822093419596006203

theorem tailTrace_2526422 : CollatzResearch.WordTrace tailWord_2526422 prefixEnd_2526422 1297268822093419596006203 := by
  unfold tailWord_2526422
  simp only [CollatzResearch.WordTrace]
  refine ⟨5759136278325752960684345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61430786968808031580633013 5759136278325752960684345)
  ·
    refine ⟨4319352208744314720513259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5759136278325752960684345 4319352208744314720513259)
    ·
      refine ⟨6479028313116472080769889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4319352208744314720513259 6479028313116472080769889)
      ·
        refine ⟨4859271234837354060577417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6479028313116472080769889 4859271234837354060577417)
        ·
          refine ⟨3644453426128015545433063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4859271234837354060577417 3644453426128015545433063)
          ·
            refine ⟨5466680139192023318149595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3644453426128015545433063 5466680139192023318149595)
            ·
              refine ⟨8200020208788034977224393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5466680139192023318149595 8200020208788034977224393)
              ·
                refine ⟨6150015156591026232918295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8200020208788034977224393 6150015156591026232918295)
                ·
                  refine ⟨9225022734886539349377443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6150015156591026232918295 9225022734886539349377443)
                  ·
                    refine ⟨13837534102329809024066165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9225022734886539349377443 13837534102329809024066165)
                    ·
                      refine ⟨1297268822093419596006203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13837534102329809024066165 1297268822093419596006203)
                      ·
                        rfl

theorem cell23_2526422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_2526422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2526422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2526422 prefixEnd_2526422 := by exact prefixLift 2526422
  have htrace : WordTrace (prefixWord ++ tailWord_2526422) baseStart_2526422 baseEnd_2526422 := by
    simpa [prefixWord, tailWord_2526422, baseEnd_2526422] using wordTrace_append hprefix tailTrace_2526422
  have hstable : (prefixWord ++ tailWord_2526422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526422).length < 2 ^ (prefixWord ++ tailWord_2526422).sum := by decide
  have hdescent : baseEnd_2526422 < baseStart_2526422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526429 : List Nat := [1, 4, 3, 2, 2, 1, 3, 1, 2, 4]
def baseStart_2526429 : Nat := 118140960795 + 2526429 * 2 ^ 59
def prefixEnd_2526429 : Nat := 4983230072969 + 3 ^ 40 * 2526429 * 2
def baseEnd_2526429 : Nat := 432424138819333689539557

theorem tailTrace_2526429 : CollatzResearch.WordTrace tailWord_2526429 prefixEnd_2526429 432424138819333689539557 := by
  unfold tailWord_2526429
  simp only [CollatzResearch.WordTrace]
  refine ⟨92146435764186687566454341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61430957176124458377636227 92146435764186687566454341)
  ·
    refine ⟨17277456705785003918710189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92146435764186687566454341 17277456705785003918710189)
    ·
      refine ⟨6479046264669376469516321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17277456705785003918710189 6479046264669376469516321)
      ·
        refine ⟨4859284698502032352137241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6479046264669376469516321 4859284698502032352137241)
        ·
          refine ⟨3644463523876524264102931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4859284698502032352137241 3644463523876524264102931)
          ·
            refine ⟨5466695285814786396154397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3644463523876524264102931 5466695285814786396154397)
            ·
              refine ⟨2050010732180544898557899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5466695285814786396154397 2050010732180544898557899)
              ·
                refine ⟨3075016098270817347836849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2050010732180544898557899 3075016098270817347836849)
                ·
                  refine ⟨2306262073703113010877637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3075016098270817347836849 2306262073703113010877637)
                  ·
                    refine ⟨432424138819333689539557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2306262073703113010877637 432424138819333689539557)
                    ·
                      rfl

theorem cell23_2526429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_2526429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2526429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2526429 prefixEnd_2526429 := by exact prefixLift 2526429
  have htrace : WordTrace (prefixWord ++ tailWord_2526429) baseStart_2526429 baseEnd_2526429 := by
    simpa [prefixWord, tailWord_2526429, baseEnd_2526429] using wordTrace_append hprefix tailTrace_2526429
  have hstable : (prefixWord ++ tailWord_2526429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526429).length < 2 ^ (prefixWord ++ tailWord_2526429).sum := by decide
  have hdescent : baseEnd_2526429 < baseStart_2526429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526496 : List Nat := [2, 1, 1, 5, 4, 1, 1, 2, 1, 3, 2]
def baseStart_2526496 : Nat := 118140960795 + 2526496 * 2 ^ 59
def prefixEnd_2526496 : Nat := 4983230072969 + 3 ^ 40 * 2526496 * 2
def baseEnd_2526496 : Nat := 1297306819661852306480863

theorem tailTrace_2526496 : CollatzResearch.WordTrace tailWord_2526496 prefixEnd_2526496 1297306819661852306480863 := by
  unfold tailWord_2526496
  simp only [CollatzResearch.WordTrace]
  refine ⟨46074439727471979004571671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61432586303295972006095561 46074439727471979004571671)
  ·
    refine ⟨69111659591207968506857507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46074439727471979004571671 69111659591207968506857507)
    ·
      refine ⟨103667489386811952760286261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69111659591207968506857507 103667489386811952760286261)
      ·
        refine ⟨9718827130013620571276837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 103667489386811952760286261 9718827130013620571276837)
        ·
          refine ⟨1822280086877553857114407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9718827130013620571276837 1822280086877553857114407)
          ·
            refine ⟨2733420130316330785671611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1822280086877553857114407 2733420130316330785671611)
            ·
              refine ⟨4100130195474496178507417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2733420130316330785671611 4100130195474496178507417)
              ·
                refine ⟨3075097646605872133880563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4100130195474496178507417 3075097646605872133880563)
                ·
                  refine ⟨4612646469908808200820845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3075097646605872133880563 4612646469908808200820845)
                  ·
                    refine ⟨1729742426215803075307817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4612646469908808200820845 1729742426215803075307817)
                    ·
                      refine ⟨1297306819661852306480863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1729742426215803075307817 1297306819661852306480863)
                      ·
                        rfl

theorem cell23_2526496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_2526496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2526496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2526496 prefixEnd_2526496 := by exact prefixLift 2526496
  have htrace : WordTrace (prefixWord ++ tailWord_2526496) baseStart_2526496 baseEnd_2526496 := by
    simpa [prefixWord, tailWord_2526496, baseEnd_2526496] using wordTrace_append hprefix tailTrace_2526496
  have hstable : (prefixWord ++ tailWord_2526496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526496).length < 2 ^ (prefixWord ++ tailWord_2526496).sum := by decide
  have hdescent : baseEnd_2526496 < baseStart_2526496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526508 : List Nat := [2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 3]
def baseStart_2526508 : Nat := 118140960795 + 2526508 * 2 ^ 59
def prefixEnd_2526508 : Nat := 4983230072969 + 3 ^ 40 * 2526508 * 2
def baseEnd_2526508 : Nat := 1297312981429706259530807

theorem tailTrace_2526508 : CollatzResearch.WordTrace tailWord_2526508 prefixEnd_2526508 1297312981429706259530807 := by
  unfold tailWord_2526508
  simp only [CollatzResearch.WordTrace]
  refine ⟨46074658565450242029290089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61432878087266989372386785 46074658565450242029290089)
  ·
    refine ⟨34555993924087681521967567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46074658565450242029290089 34555993924087681521967567)
    ·
      refine ⟨51833990886131522282951351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34555993924087681521967567 51833990886131522282951351)
      ·
        refine ⟨77750986329197283424427027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51833990886131522282951351 77750986329197283424427027)
        ·
          refine ⟨116626479493795925136640541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77750986329197283424427027 116626479493795925136640541)
          ·
            refine ⟨43734929810173471926240203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116626479493795925136640541 43734929810173471926240203)
            ·
              refine ⟨65602394715260207889360305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43734929810173471926240203 65602394715260207889360305)
              ·
                refine ⟨49201796036445155917020229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65602394715260207889360305 49201796036445155917020229)
                ·
                  refine ⟨9225336756833466734441293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49201796036445155917020229 9225336756833466734441293)
                  ·
                    refine ⟨3459501283812550025415485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9225336756833466734441293 3459501283812550025415485)
                    ·
                      refine ⟨1297312981429706259530807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3459501283812550025415485 1297312981429706259530807)
                      ·
                        rfl

theorem cell23_2526508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 3].length) (baseStart_2526508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2526508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2526508 prefixEnd_2526508 := by exact prefixLift 2526508
  have htrace : WordTrace (prefixWord ++ tailWord_2526508) baseStart_2526508 baseEnd_2526508 := by
    simpa [prefixWord, tailWord_2526508, baseEnd_2526508] using wordTrace_append hprefix tailTrace_2526508
  have hstable : (prefixWord ++ tailWord_2526508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526508).length < 2 ^ (prefixWord ++ tailWord_2526508).sum := by decide
  have hdescent : baseEnd_2526508 < baseStart_2526508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526509 : List Nat := [1, 5, 3, 1, 1, 2, 1, 2, 1, 4, 2]
def baseStart_2526509 : Nat := 118140960795 + 2526509 * 2 ^ 59
def prefixEnd_2526509 : Nat := 4983230072969 + 3 ^ 40 * 2526509 * 2
def baseEnd_2526509 : Nat := 1297313494910360755618303

theorem tailTrace_2526509 : CollatzResearch.WordTrace tailWord_2526509 prefixEnd_2526509 1297313494910360755618303 := by
  unfold tailWord_2526509
  simp only [CollatzResearch.WordTrace]
  refine ⟨92149353603896861229366581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61432902402597907486244387 92149353603896861229366581)
  ·
    refine ⟨8639001900365330740253117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 92149353603896861229366581 8639001900365330740253117)
    ·
      refine ⟨3239625712636999027594919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8639001900365330740253117 3239625712636999027594919)
      ·
        refine ⟨4859438568955498541392379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3239625712636999027594919 4859438568955498541392379)
        ·
          refine ⟨7289157853433247812088569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4859438568955498541392379 7289157853433247812088569)
          ·
            refine ⟨5466868390074935859066427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7289157853433247812088569 5466868390074935859066427)
            ·
              refine ⟨8200302585112403788599641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5466868390074935859066427 8200302585112403788599641)
              ·
                refine ⟨6150226938834302841449731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8200302585112403788599641 6150226938834302841449731)
                ·
                  refine ⟨9225340408251454262174597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6150226938834302841449731 9225340408251454262174597)
                  ·
                    refine ⟨1729751326547147674157737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9225340408251454262174597 1729751326547147674157737)
                    ·
                      refine ⟨1297313494910360755618303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1729751326547147674157737 1297313494910360755618303)
                      ·
                        rfl

theorem cell23_2526509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_2526509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2526509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2526509 prefixEnd_2526509 := by exact prefixLift 2526509
  have htrace : WordTrace (prefixWord ++ tailWord_2526509) baseStart_2526509 baseEnd_2526509 := by
    simpa [prefixWord, tailWord_2526509, baseEnd_2526509] using wordTrace_append hprefix tailTrace_2526509
  have hstable : (prefixWord ++ tailWord_2526509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526509).length < 2 ^ (prefixWord ++ tailWord_2526509).sum := by decide
  have hdescent : baseEnd_2526509 < baseStart_2526509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526528 : List Nat := [2, 1, 1, 2, 2, 1, 3, 4, 2, 5]
def baseStart_2526528 : Nat := 118140960795 + 2526528 * 2 ^ 59
def prefixEnd_2526528 : Nat := 4983230072969 + 3 ^ 40 * 2526528 * 2
def baseEnd_2526528 : Nat := 432441083680932060426905

theorem tailTrace_2526528 : CollatzResearch.WordTrace tailWord_2526528 prefixEnd_2526528 432441083680932060426905 := by
  unfold tailWord_2526528
  simp only [CollatzResearch.WordTrace]
  refine ⟨46075023295414013737154119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61433364393885351649538825 46075023295414013737154119)
  ·
    refine ⟨69112534943121020605731179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46075023295414013737154119 69112534943121020605731179)
    ·
      refine ⟨103668802414681530908596769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69112534943121020605731179 103668802414681530908596769)
      ·
        refine ⟨77751601811011148181447577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103668802414681530908596769 77751601811011148181447577)
        ·
          refine ⟨58313701358258361136085683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77751601811011148181447577 58313701358258361136085683)
          ·
            refine ⟨87470552037387541704128525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58313701358258361136085683 87470552037387541704128525)
            ·
              refine ⟨32801457014020328139048197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87470552037387541704128525 32801457014020328139048197)
              ·
                refine ⟨6150273190128811526071537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32801457014020328139048197 6150273190128811526071537)
                ·
                  refine ⟨4612704892596608644553653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6150273190128811526071537 4612704892596608644553653)
                  ·
                    refine ⟨432441083680932060426905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4612704892596608644553653 432441083680932060426905)
                    ·
                      rfl

theorem cell23_2526528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4, 2, 5].length) (baseStart_2526528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2526528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2526528 prefixEnd_2526528 := by exact prefixLift 2526528
  have htrace : WordTrace (prefixWord ++ tailWord_2526528) baseStart_2526528 baseEnd_2526528 := by
    simpa [prefixWord, tailWord_2526528, baseEnd_2526528] using wordTrace_append hprefix tailTrace_2526528
  have hstable : (prefixWord ++ tailWord_2526528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526528).length < 2 ^ (prefixWord ++ tailWord_2526528).sum := by decide
  have hdescent : baseEnd_2526528 < baseStart_2526528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526535 : List Nat := [1, 1, 4, 1, 2, 3, 1, 1, 2, 5, 2]
def baseStart_2526535 : Nat := 118140960795 + 2526535 * 2 ^ 59
def prefixEnd_2526535 : Nat := 4983230072969 + 3 ^ 40 * 2526535 * 2
def baseEnd_2526535 : Nat := 1297326845407377653893183

theorem tailTrace_2526535 : CollatzResearch.WordTrace tailWord_2526535 prefixEnd_2526535 1297326845407377653893183 := by
  unfold tailWord_2526535
  simp only [CollatzResearch.WordTrace]
  refine ⟨92150301901802667669813059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61433534601201778446542039 92150301901802667669813059)
  ·
    refine ⟨138225452852704001504719589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92150301901802667669813059 138225452852704001504719589)
    ·
      refine ⟨25917272409882000282134923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 138225452852704001504719589 25917272409882000282134923)
      ·
        refine ⟨38875908614823000423202385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25917272409882000282134923 38875908614823000423202385)
        ·
          refine ⟨29156931461117250317401789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38875908614823000423202385 29156931461117250317401789)
          ·
            refine ⟨10933849297918968869025671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29156931461117250317401789 10933849297918968869025671)
            ·
              refine ⟨16400773946878453303538507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10933849297918968869025671 16400773946878453303538507)
              ·
                refine ⟨24601160920317679955307761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16400773946878453303538507 24601160920317679955307761)
                ·
                  refine ⟨18450870690238259966480821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24601160920317679955307761 18450870690238259966480821)
                  ·
                    refine ⟨1729769127209836871857577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18450870690238259966480821 1729769127209836871857577)
                    ·
                      refine ⟨1297326845407377653893183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1729769127209836871857577 1297326845407377653893183)
                      ·
                        rfl

theorem cell23_2526535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 5, 2].length) (baseStart_2526535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2526535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2526535 prefixEnd_2526535 := by exact prefixLift 2526535
  have htrace : WordTrace (prefixWord ++ tailWord_2526535) baseStart_2526535 baseEnd_2526535 := by
    simpa [prefixWord, tailWord_2526535, baseEnd_2526535] using wordTrace_append hprefix tailTrace_2526535
  have hstable : (prefixWord ++ tailWord_2526535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526535).length < 2 ^ (prefixWord ++ tailWord_2526535).sum := by decide
  have hdescent : baseEnd_2526535 < baseStart_2526535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526565 : List Nat := [1, 3, 1, 3, 1, 2, 1, 2, 1, 6, 2]
def baseStart_2526565 : Nat := 118140960795 + 2526565 * 2 ^ 59
def prefixEnd_2526565 : Nat := 4983230072969 + 3 ^ 40 * 2526565 * 2
def baseEnd_2526565 : Nat := 1297342249827012536518045

theorem tailTrace_2526565 : CollatzResearch.WordTrace tailWord_2526565 prefixEnd_2526565 1297342249827012536518045 := by
  unfold tailWord_2526565
  simp only [CollatzResearch.WordTrace]
  refine ⟨92151396091693982793405149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61434264061129321862270099 92151396091693982793405149)
  ·
    refine ⟨34556773534385243547526931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92151396091693982793405149 34556773534385243547526931)
    ·
      refine ⟨51835160301577865321290397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34556773534385243547526931 51835160301577865321290397)
      ·
        refine ⟨19438185113091699495483899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51835160301577865321290397 19438185113091699495483899)
        ·
          refine ⟨29157277669637549243225849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19438185113091699495483899 29157277669637549243225849)
          ·
            refine ⟨21867958252228161932419387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29157277669637549243225849 21867958252228161932419387)
            ·
              refine ⟨32801937378342242898629081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21867958252228161932419387 32801937378342242898629081)
              ·
                refine ⟨24601453033756682173971811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32801937378342242898629081 24601453033756682173971811)
                ·
                  refine ⟨36902179550635023260957717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24601453033756682173971811 36902179550635023260957717)
                  ·
                    refine ⟨1729789666436016715357393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 36902179550635023260957717 1729789666436016715357393)
                    ·
                      refine ⟨1297342249827012536518045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1729789666436016715357393 1297342249827012536518045)
                      ·
                        rfl

theorem cell23_2526565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 6, 2].length) (baseStart_2526565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2526565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2526565 prefixEnd_2526565 := by exact prefixLift 2526565
  have htrace : WordTrace (prefixWord ++ tailWord_2526565) baseStart_2526565 baseEnd_2526565 := by
    simpa [prefixWord, tailWord_2526565, baseEnd_2526565] using wordTrace_append hprefix tailTrace_2526565
  have hstable : (prefixWord ++ tailWord_2526565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526565).length < 2 ^ (prefixWord ++ tailWord_2526565).sum := by decide
  have hdescent : baseEnd_2526565 < baseStart_2526565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526578 : List Nat := [3, 2, 1, 2, 1, 2, 1, 1, 1, 3, 6]
def baseStart_2526578 : Nat := 118140960795 + 2526578 * 2 ^ 59
def prefixEnd_2526578 : Nat := 4983230072969 + 3 ^ 40 * 2526578 * 2
def baseEnd_2526578 : Nat := 1297348925075520985655485

theorem tailTrace_2526578 : CollatzResearch.WordTrace tailWord_2526578 prefixEnd_2526578 1297348925075520985655485 := by
  unfold tailWord_2526578
  simp only [CollatzResearch.WordTrace]
  refine ⟨23037967560161721503407097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61434580160431257342418925 23037967560161721503407097)
  ·
    refine ⟨17278475670121291127555323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23037967560161721503407097 17278475670121291127555323)
    ·
      refine ⟨25917713505181936691332985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17278475670121291127555323 25917713505181936691332985)
      ·
        refine ⟨19438285128886452518499739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25917713505181936691332985 19438285128886452518499739)
        ·
          refine ⟨29157427693329678777749609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19438285128886452518499739 29157427693329678777749609)
          ·
            refine ⟨21868070769997259083312207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29157427693329678777749609 21868070769997259083312207)
            ·
              refine ⟨32802106154995888624968311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21868070769997259083312207 32802106154995888624968311)
              ·
                refine ⟨49203159232493832937452467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32802106154995888624968311 49203159232493832937452467)
                ·
                  refine ⟨73804738848740749406178701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49203159232493832937452467 73804738848740749406178701)
                  ·
                    refine ⟨27676777068277781027317013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 73804738848740749406178701 27676777068277781027317013)
                    ·
                      refine ⟨1297348925075520985655485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27676777068277781027317013 1297348925075520985655485)
                      ·
                        rfl

theorem cell23_2526578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_2526578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2526578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2526578 prefixEnd_2526578 := by exact prefixLift 2526578
  have htrace : WordTrace (prefixWord ++ tailWord_2526578) baseStart_2526578 baseEnd_2526578 := by
    simpa [prefixWord, tailWord_2526578, baseEnd_2526578] using wordTrace_append hprefix tailTrace_2526578
  have hstable : (prefixWord ++ tailWord_2526578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526578).length < 2 ^ (prefixWord ++ tailWord_2526578).sum := by decide
  have hdescent : baseEnd_2526578 < baseStart_2526578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526585 : List Nat := [1, 2, 1, 3, 2, 1, 2, 4, 2, 2, 3]
def baseStart_2526585 : Nat := 118140960795 + 2526585 * 2 ^ 59
def prefixEnd_2526585 : Nat := 4983230072969 + 3 ^ 40 * 2526585 * 2
def baseEnd_2526585 : Nat := 1297352519440102458267953

theorem tailTrace_2526585 : CollatzResearch.WordTrace tailWord_2526585 prefixEnd_2526585 1297352519440102458267953 := by
  unfold tailWord_2526585
  simp only [CollatzResearch.WordTrace]
  refine ⟨92152125551621526209133209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61434750367747684139422139 92152125551621526209133209)
  ·
    refine ⟨69114094163716144656849907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92152125551621526209133209 69114094163716144656849907)
    ·
      refine ⟨103671141245574216985274861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69114094163716144656849907 103671141245574216985274861)
      ·
        refine ⟨38876677967090331369478073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103671141245574216985274861 38876677967090331369478073)
        ·
          refine ⟨29157508475317748527108555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38876677967090331369478073 29157508475317748527108555)
          ·
            refine ⟨43736262712976622790662833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29157508475317748527108555 43736262712976622790662833)
            ·
              refine ⟨32802197034732467092997125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43736262712976622790662833 32802197034732467092997125)
              ·
                refine ⟨6150411944012337579936961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32802197034732467092997125 6150411944012337579936961)
                ·
                  refine ⟨4612808958009253184952721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6150411944012337579936961 4612808958009253184952721)
                  ·
                    refine ⟨3459606718506939888714541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4612808958009253184952721 3459606718506939888714541)
                    ·
                      refine ⟨1297352519440102458267953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3459606718506939888714541 1297352519440102458267953)
                      ·
                        rfl

theorem cell23_2526585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4, 2, 2, 3].length) (baseStart_2526585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2526585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2526585 prefixEnd_2526585 := by exact prefixLift 2526585
  have htrace : WordTrace (prefixWord ++ tailWord_2526585) baseStart_2526585 baseEnd_2526585 := by
    simpa [prefixWord, tailWord_2526585, baseEnd_2526585] using wordTrace_append hprefix tailTrace_2526585
  have hstable : (prefixWord ++ tailWord_2526585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526585).length < 2 ^ (prefixWord ++ tailWord_2526585).sum := by decide
  have hdescent : baseEnd_2526585 < baseStart_2526585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526588 : List Nat := [2, 2, 2, 1, 1, 1, 5, 1, 8]
def baseStart_2526588 : Nat := 118140960795 + 2526588 * 2 ^ 59
def prefixEnd_2526588 : Nat := 4983230072969 + 3 ^ 40 * 2526588 * 2
def baseEnd_2526588 : Nat := 144150451098007327392271

theorem tailTrace_2526588 : CollatzResearch.WordTrace tailWord_2526588 prefixEnd_2526588 144150451098007327392271 := by
  unfold tailWord_2526588
  simp only [CollatzResearch.WordTrace]
  refine ⟨46076117485305328860746209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61434823313740438480994945 46076117485305328860746209)
  ·
    refine ⟨34557088113978996645559657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46076117485305328860746209 34557088113978996645559657)
    ·
      refine ⟨25917816085484247484169743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34557088113978996645559657 25917816085484247484169743)
      ·
        refine ⟨38876724128226371226254615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25917816085484247484169743 38876724128226371226254615)
        ·
          refine ⟨58315086192339556839381923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38876724128226371226254615 58315086192339556839381923)
          ·
            refine ⟨87472629288509335259072885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58315086192339556839381923 87472629288509335259072885)
            ·
              refine ⟨8200558995797750180538083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 87472629288509335259072885 8200558995797750180538083)
              ·
                refine ⟨12300838493696625270807125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8200558995797750180538083 12300838493696625270807125)
                ·
                  refine ⟨144150451098007327392271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12300838493696625270807125 144150451098007327392271)
                  ·
                    rfl

theorem cell23_2526588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 8].length) (baseStart_2526588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2526588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2526588 prefixEnd_2526588 := by exact prefixLift 2526588
  have htrace : WordTrace (prefixWord ++ tailWord_2526588) baseStart_2526588 baseEnd_2526588 := by
    simpa [prefixWord, tailWord_2526588, baseEnd_2526588] using wordTrace_append hprefix tailTrace_2526588
  have hstable : (prefixWord ++ tailWord_2526588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526588).length < 2 ^ (prefixWord ++ tailWord_2526588).sum := by decide
  have hdescent : baseEnd_2526588 < baseStart_2526588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526626 : List Nat := [3, 3, 1, 2, 1, 4, 1, 3, 1, 4]
def baseStart_2526626 : Nat := 118140960795 + 2526626 * 2 ^ 59
def prefixEnd_2526626 : Nat := 4983230072969 + 3 ^ 40 * 2526626 * 2
def baseEnd_2526626 : Nat := 432457857382312265951755

theorem tailTrace_2526626 : CollatzResearch.WordTrace tailWord_2526626 prefixEnd_2526626 432457857382312265951755 := by
  unfold tailWord_2526626
  simp only [CollatzResearch.WordTrace]
  refine ⟨23038405236118247552843933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61435747296315326807583821 23038405236118247552843933)
  ·
    refine ⟨8639401963544342832316475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23038405236118247552843933 8639401963544342832316475)
    ·
      refine ⟨12959102945316514248474713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8639401963544342832316475 12959102945316514248474713)
      ·
        refine ⟨9719327208987385686356035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12959102945316514248474713 9719327208987385686356035)
        ·
          refine ⟨14578990813481078529534053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9719327208987385686356035 14578990813481078529534053)
          ·
            refine ⟨2733560777527702224287635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14578990813481078529534053 2733560777527702224287635)
            ·
              refine ⟨4100341166291553336431453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2733560777527702224287635 4100341166291553336431453)
              ·
                refine ⟨1537627937359332501161795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4100341166291553336431453 1537627937359332501161795)
                ·
                  refine ⟨2306441906038998751742693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1537627937359332501161795 2306441906038998751742693)
                  ·
                    refine ⟨432457857382312265951755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2306441906038998751742693 432457857382312265951755)
                    ·
                      rfl

theorem cell23_2526626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 3, 1, 4].length) (baseStart_2526626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2526626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2526626 prefixEnd_2526626 := by exact prefixLift 2526626
  have htrace : WordTrace (prefixWord ++ tailWord_2526626) baseStart_2526626 baseEnd_2526626 := by
    simpa [prefixWord, tailWord_2526626, baseEnd_2526626] using wordTrace_append hprefix tailTrace_2526626
  have hstable : (prefixWord ++ tailWord_2526626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526626).length < 2 ^ (prefixWord ++ tailWord_2526626).sum := by decide
  have hdescent : baseEnd_2526626 < baseStart_2526626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526676 : List Nat := [2, 4, 1, 2, 3, 1, 2, 1, 2, 3, 2]
def baseStart_2526676 : Nat := 118140960795 + 2526676 * 2 ^ 59
def prefixEnd_2526676 : Nat := 4983230072969 + 3 ^ 40 * 2526676 * 2
def baseEnd_2526676 : Nat := 1297399246179661602230035

theorem tailTrace_2526676 : CollatzResearch.WordTrace tailWord_2526676 prefixEnd_2526676 1297399246179661602230035 := by
  unfold tailWord_2526676
  simp only [CollatzResearch.WordTrace]
  refine ⟨46077722297145924375347941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61436963062861232500463921 46077722297145924375347941)
  ·
    refine ⟨8639572930714860820377739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46077722297145924375347941 8639572930714860820377739)
    ·
      refine ⟨12959359396072291230566609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8639572930714860820377739 12959359396072291230566609)
      ·
        refine ⟨9719519547054218422924957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12959359396072291230566609 9719519547054218422924957)
        ·
          refine ⟨3644819830145331908596859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9719519547054218422924957 3644819830145331908596859)
          ·
            refine ⟨5467229745217997862895289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3644819830145331908596859 5467229745217997862895289)
            ·
              refine ⟨4100422308913498397171467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5467229745217997862895289 4100422308913498397171467)
              ·
                refine ⟨6150633463370247595757201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4100422308913498397171467 6150633463370247595757201)
                ·
                  refine ⟨4612975097527685696817901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6150633463370247595757201 4612975097527685696817901)
                  ·
                    refine ⟨1729865661572882136306713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4612975097527685696817901 1729865661572882136306713)
                    ·
                      refine ⟨1297399246179661602230035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1729865661572882136306713 1297399246179661602230035)
                      ·
                        rfl

theorem cell23_2526676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_2526676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2526676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2526676 prefixEnd_2526676 := by exact prefixLift 2526676
  have htrace : WordTrace (prefixWord ++ tailWord_2526676) baseStart_2526676 baseEnd_2526676 := by
    simpa [prefixWord, tailWord_2526676, baseEnd_2526676] using wordTrace_append hprefix tailTrace_2526676
  have hstable : (prefixWord ++ tailWord_2526676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526676).length < 2 ^ (prefixWord ++ tailWord_2526676).sum := by decide
  have hdescent : baseEnd_2526676 < baseStart_2526676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526689 : List Nat := [1, 2, 3, 1, 2, 4, 3, 1, 1, 1, 4]
def baseStart_2526689 : Nat := 118140960795 + 2526689 * 2 ^ 59
def prefixEnd_2526689 : Nat := 4983230072969 + 3 ^ 40 * 2526689 * 2
def baseEnd_2526689 : Nat := 1297405921428170051367475

theorem tailTrace_2526689 : CollatzResearch.WordTrace tailWord_2526689 prefixEnd_2526689 1297405921428170051367475 := by
  unfold tailWord_2526689
  simp only [CollatzResearch.WordTrace]
  refine ⟨92155918743244751970919121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61437279162163167980612747 92155918743244751970919121)
  ·
    refine ⟨69116939057433563978189341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92155918743244751970919121 69116939057433563978189341)
    ·
      refine ⟨25918852146537586491821003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69116939057433563978189341 25918852146537586491821003)
      ·
        refine ⟨38878278219806379737731505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25918852146537586491821003 38878278219806379737731505)
        ·
          refine ⟨29158708664854784803298629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38878278219806379737731505 29158708664854784803298629)
          ·
            refine ⟨5467257874660272150618493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29158708664854784803298629 5467257874660272150618493)
            ·
              refine ⟨2050221702997602056481935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5467257874660272150618493 2050221702997602056481935)
              ·
                refine ⟨3075332554496403084722903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2050221702997602056481935 3075332554496403084722903)
                ·
                  refine ⟨4612998831744604627084355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3075332554496403084722903 4612998831744604627084355)
                  ·
                    refine ⟨6919498247616906940626533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4612998831744604627084355 6919498247616906940626533)
                    ·
                      refine ⟨1297405921428170051367475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6919498247616906940626533 1297405921428170051367475)
                      ·
                        rfl

theorem cell23_2526689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3, 1, 1, 1, 4].length) (baseStart_2526689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2526689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2526689 prefixEnd_2526689 := by exact prefixLift 2526689
  have htrace : WordTrace (prefixWord ++ tailWord_2526689) baseStart_2526689 baseEnd_2526689 := by
    simpa [prefixWord, tailWord_2526689, baseEnd_2526689] using wordTrace_append hprefix tailTrace_2526689
  have hstable : (prefixWord ++ tailWord_2526689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526689).length < 2 ^ (prefixWord ++ tailWord_2526689).sum := by decide
  have hdescent : baseEnd_2526689 < baseStart_2526689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526692 : List Nat := [2, 3, 1, 1, 1, 1, 1, 7, 1, 2, 3]
def baseStart_2526692 : Nat := 118140960795 + 2526692 * 2 ^ 59
def prefixEnd_2526692 : Nat := 4983230072969 + 3 ^ 40 * 2526692 * 2
def baseEnd_2526692 : Nat := 1297407461870133539629961

theorem tailTrace_2526692 : CollatzResearch.WordTrace tailWord_2526692 prefixEnd_2526692 1297407461870133539629961 := by
  unfold tailWord_2526692
  simp only [CollatzResearch.WordTrace]
  refine ⟨46078014081116941741639165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61437352108155922322185553 46078014081116941741639165)
  ·
    refine ⟨17279255280418853153114687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46078014081116941741639165 17279255280418853153114687)
    ·
      refine ⟨25918882920628279729672031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17279255280418853153114687 25918882920628279729672031)
      ·
        refine ⟨38878324380942419594508047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25918882920628279729672031 38878324380942419594508047)
        ·
          refine ⟨58317486571413629391762071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38878324380942419594508047 58317486571413629391762071)
          ·
            refine ⟨87476229857120444087643107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58317486571413629391762071 87476229857120444087643107)
            ·
              refine ⟨131214344785680666131464661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87476229857120444087643107 131214344785680666131464661)
              ·
                refine ⟨3075336205914390612456203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 131214344785680666131464661 3075336205914390612456203)
                ·
                  refine ⟨4613004308871585918684305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3075336205914390612456203 4613004308871585918684305)
                  ·
                    refine ⟨3459753231653689439013229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4613004308871585918684305 3459753231653689439013229)
                    ·
                      refine ⟨1297407461870133539629961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3459753231653689439013229 1297407461870133539629961)
                      ·
                        rfl

theorem cell23_2526692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 7, 1, 2, 3].length) (baseStart_2526692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2526692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2526692 prefixEnd_2526692 := by exact prefixLift 2526692
  have htrace : WordTrace (prefixWord ++ tailWord_2526692) baseStart_2526692 baseEnd_2526692 := by
    simpa [prefixWord, tailWord_2526692, baseEnd_2526692] using wordTrace_append hprefix tailTrace_2526692
  have hstable : (prefixWord ++ tailWord_2526692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526692).length < 2 ^ (prefixWord ++ tailWord_2526692).sum := by decide
  have hdescent : baseEnd_2526692 < baseStart_2526692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526709 : List Nat := [1, 3, 5, 1, 1, 1, 1, 2, 3, 2, 3]
def baseStart_2526709 : Nat := 118140960795 + 2526709 * 2 ^ 59
def prefixEnd_2526709 : Nat := 4983230072969 + 3 ^ 40 * 2526709 * 2
def baseEnd_2526709 : Nat := 1297416191041259973117383

theorem tailTrace_2526709 : CollatzResearch.WordTrace tailWord_2526709 prefixEnd_2526709 1297416191041259973117383 := by
  unfold tailWord_2526709
  simp only [CollatzResearch.WordTrace]
  refine ⟨92156648203172295386647181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61437765468781530257764787 92156648203172295386647181)
  ·
    refine ⟨34558743076189610769992693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92156648203172295386647181 34558743076189610769992693)
    ·
      refine ⟨3239882163392776009686815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34558743076189610769992693 3239882163392776009686815)
      ·
        refine ⟨4859823245089164014530223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3239882163392776009686815 4859823245089164014530223)
        ·
          refine ⟨7289734867633746021795335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4859823245089164014530223 7289734867633746021795335)
          ·
            refine ⟨10934602301450619032693003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7289734867633746021795335 10934602301450619032693003)
            ·
              refine ⟨16401903452175928549039505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10934602301450619032693003 16401903452175928549039505)
              ·
                refine ⟨12301427589131946411779629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16401903452175928549039505 12301427589131946411779629)
                ·
                  refine ⟨4613035345924479904417361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12301427589131946411779629 4613035345924479904417361)
                  ·
                    refine ⟨3459776509443359928313021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4613035345924479904417361 3459776509443359928313021)
                    ·
                      refine ⟨1297416191041259973117383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3459776509443359928313021 1297416191041259973117383)
                      ·
                        rfl

theorem cell23_2526709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_2526709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2526709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2526709 prefixEnd_2526709 := by exact prefixLift 2526709
  have htrace : WordTrace (prefixWord ++ tailWord_2526709) baseStart_2526709 baseEnd_2526709 := by
    simpa [prefixWord, tailWord_2526709, baseEnd_2526709] using wordTrace_append hprefix tailTrace_2526709
  have hstable : (prefixWord ++ tailWord_2526709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526709).length < 2 ^ (prefixWord ++ tailWord_2526709).sum := by decide
  have hdescent : baseEnd_2526709 < baseStart_2526709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526740 : List Nat := [2, 4, 3, 1, 3, 1, 2, 1, 1, 1, 4]
def baseStart_2526740 : Nat := 118140960795 + 2526740 * 2 ^ 59
def prefixEnd_2526740 : Nat := 4983230072969 + 3 ^ 40 * 2526740 * 2
def baseEnd_2526740 : Nat := 1297432108941549351829741

theorem tailTrace_2526740 : CollatzResearch.WordTrace tailWord_2526740 prefixEnd_2526740 1297432108941549351829741 := by
  unfold tailWord_2526740
  simp only [CollatzResearch.WordTrace]
  refine ⟨46078889433029993840512837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61438519244039991787350449 46078889433029993840512837)
  ·
    refine ⟨8639791768693123845096157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46078889433029993840512837 8639791768693123845096157)
    ·
      refine ⟨3239921913259921441911059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8639791768693123845096157 3239921913259921441911059)
      ·
        refine ⟨4859882869889882162866589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3239921913259921441911059 4859882869889882162866589)
        ·
          refine ⟨1822456076208705811074971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4859882869889882162866589 1822456076208705811074971)
          ·
            refine ⟨2733684114313058716612457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1822456076208705811074971 2733684114313058716612457)
            ·
              refine ⟨2050263085734794037459343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2733684114313058716612457 2050263085734794037459343)
              ·
                refine ⟨3075394628602191056189015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2050263085734794037459343 3075394628602191056189015)
                ·
                  refine ⟨4613091942903286584283523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3075394628602191056189015 4613091942903286584283523)
                  ·
                    refine ⟨6919637914354929876425285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4613091942903286584283523 6919637914354929876425285)
                    ·
                      refine ⟨1297432108941549351829741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6919637914354929876425285 1297432108941549351829741)
                      ·
                        rfl

theorem cell23_2526740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_2526740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2526740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2526740 prefixEnd_2526740 := by exact prefixLift 2526740
  have htrace : WordTrace (prefixWord ++ tailWord_2526740) baseStart_2526740 baseEnd_2526740 := by
    simpa [prefixWord, tailWord_2526740, baseEnd_2526740] using wordTrace_append hprefix tailTrace_2526740
  have hstable : (prefixWord ++ tailWord_2526740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526740).length < 2 ^ (prefixWord ++ tailWord_2526740).sum := by decide
  have hdescent : baseEnd_2526740 < baseStart_2526740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526825 : List Nat := [1, 2, 1, 1, 1, 4, 3, 1, 1, 1, 7]
def baseStart_2526825 : Nat := 118140960795 + 2526825 * 2 ^ 59
def prefixEnd_2526825 : Nat := 4983230072969 + 3 ^ 40 * 2526825 * 2
def baseEnd_2526825 : Nat := 1297475754797181519266849

theorem tailTrace_2526825 : CollatzResearch.WordTrace tailWord_2526825 prefixEnd_2526825 1297475754797181519266849 := by
  unfold tailWord_2526825
  simp only [CollatzResearch.WordTrace]
  refine ⟨92160879070752047197869929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61440586047168031465246619 92160879070752047197869929)
  ·
    refine ⟨69120659303064035398402447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92160879070752047197869929 69120659303064035398402447)
    ·
      refine ⟨103680988954596053097603671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69120659303064035398402447 103680988954596053097603671)
      ·
        refine ⟨155521483431894079646405507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103680988954596053097603671 155521483431894079646405507)
        ·
          refine ⟨233282225147841119469608261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155521483431894079646405507 233282225147841119469608261)
          ·
            refine ⟨43740417215220209900551549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 233282225147841119469608261 43740417215220209900551549)
            ·
              refine ⟨16402656455707578712706831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43740417215220209900551549 16402656455707578712706831)
              ·
                refine ⟨24603984683561368069060247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16402656455707578712706831 24603984683561368069060247)
                ·
                  refine ⟨36905977025342052103590371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24603984683561368069060247 36905977025342052103590371)
                  ·
                    refine ⟨55358965538013078155385557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36905977025342052103590371 55358965538013078155385557)
                    ·
                      refine ⟨1297475754797181519266849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 55358965538013078155385557 1297475754797181519266849)
                      ·
                        rfl

theorem cell23_2526825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 1, 7].length) (baseStart_2526825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2526825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2526825 prefixEnd_2526825 := by exact prefixLift 2526825
  have htrace : WordTrace (prefixWord ++ tailWord_2526825) baseStart_2526825 baseEnd_2526825 := by
    simpa [prefixWord, tailWord_2526825, baseEnd_2526825] using wordTrace_append hprefix tailTrace_2526825
  have hstable : (prefixWord ++ tailWord_2526825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526825).length < 2 ^ (prefixWord ++ tailWord_2526825).sum := by decide
  have hdescent : baseEnd_2526825 < baseStart_2526825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526849 : List Nat := [1, 2, 4, 2, 1, 3, 2, 1, 2, 5]
def baseStart_2526849 : Nat := 118140960795 + 2526849 * 2 ^ 59
def prefixEnd_2526849 : Nat := 4983230072969 + 3 ^ 40 * 2526849 * 2
def baseEnd_2526849 : Nat := 432496026110963141788913

theorem tailTrace_2526849 : CollatzResearch.WordTrace tailWord_2526849 prefixEnd_2526849 432496026110963141788913 := by
  unfold tailWord_2526849
  simp only [CollatzResearch.WordTrace]
  refine ⟨92161754422665099296743601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61441169615110066197829067 92161754422665099296743601)
  ·
    refine ⟨69121315816998824472557701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92161754422665099296743601 69121315816998824472557701)
    ·
      refine ⟨12960246715687279588604569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69121315816998824472557701 12960246715687279588604569)
      ·
        refine ⟨9720185036765459691453427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12960246715687279588604569 9720185036765459691453427)
        ·
          refine ⟨14580277555148189537180141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9720185036765459691453427 14580277555148189537180141)
          ·
            refine ⟨5467604083180571076442553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14580277555148189537180141 5467604083180571076442553)
            ·
              refine ⟨4100703062385428307331915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5467604083180571076442553 4100703062385428307331915)
              ·
                refine ⟨6151054593578142460997873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4100703062385428307331915 6151054593578142460997873)
                ·
                  refine ⟨4613290945183606845748405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6151054593578142460997873 4613290945183606845748405)
                  ·
                    refine ⟨432496026110963141788913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4613290945183606845748405 432496026110963141788913)
                    ·
                      rfl

theorem cell23_2526849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_2526849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2526849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2526849 prefixEnd_2526849 := by exact prefixLift 2526849
  have htrace : WordTrace (prefixWord ++ tailWord_2526849) baseStart_2526849 baseEnd_2526849 := by
    simpa [prefixWord, tailWord_2526849, baseEnd_2526849] using wordTrace_append hprefix tailTrace_2526849
  have hstable : (prefixWord ++ tailWord_2526849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526849).length < 2 ^ (prefixWord ++ tailWord_2526849).sum := by decide
  have hdescent : baseEnd_2526849 < baseStart_2526849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526906 : List Nat := [3, 1, 1, 1, 2, 6, 1, 1, 2, 2, 3]
def baseStart_2526906 : Nat := 118140960795 + 2526906 * 2 ^ 59
def prefixEnd_2526906 : Nat := 4983230072969 + 3 ^ 40 * 2526906 * 2
def baseEnd_2526906 : Nat := 1297517346730195702353977

theorem tailTrace_2526906 : CollatzResearch.WordTrace tailWord_2526906 prefixEnd_2526906 1297517346730195702353977 := by
  unfold tailWord_2526906
  simp only [CollatzResearch.WordTrace]
  refine ⟨23040958345864649507892143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61442555588972398687712381 23040958345864649507892143)
  ·
    refine ⟨34561437518796974261838215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23040958345864649507892143 34561437518796974261838215)
    ·
      refine ⟨51842156278195461392757323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34561437518796974261838215 51842156278195461392757323)
      ·
        refine ⟨77763234417293192089135985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51842156278195461392757323 77763234417293192089135985)
        ·
          refine ⟨58322425812969894066851989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77763234417293192089135985 58322425812969894066851989)
          ·
            refine ⟨2733863709982963784383687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 58322425812969894066851989 2733863709982963784383687)
            ·
              refine ⟨4100795564974445676575531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2733863709982963784383687 4100795564974445676575531)
              ·
                refine ⟨6151193347461668514863297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4100795564974445676575531 6151193347461668514863297)
                ·
                  refine ⟨4613395010596251386147473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6151193347461668514863297 4613395010596251386147473)
                  ·
                    refine ⟨3460046257947188539610605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4613395010596251386147473 3460046257947188539610605)
                    ·
                      refine ⟨1297517346730195702353977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3460046257947188539610605 1297517346730195702353977)
                      ·
                        rfl

theorem cell23_2526906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 1, 2, 2, 3].length) (baseStart_2526906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2526906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2526906 prefixEnd_2526906 := by exact prefixLift 2526906
  have htrace : WordTrace (prefixWord ++ tailWord_2526906) baseStart_2526906 baseEnd_2526906 := by
    simpa [prefixWord, tailWord_2526906, baseEnd_2526906] using wordTrace_append hprefix tailTrace_2526906
  have hstable : (prefixWord ++ tailWord_2526906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526906).length < 2 ^ (prefixWord ++ tailWord_2526906).sum := by decide
  have hdescent : baseEnd_2526906 < baseStart_2526906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526919 : List Nat := [1, 1, 4, 1, 1, 1, 3, 2, 5, 1, 3]
def baseStart_2526919 : Nat := 118140960795 + 2526919 * 2 ^ 59
def prefixEnd_2526919 : Nat := 4983230072969 + 3 ^ 40 * 2526919 * 2
def baseEnd_2526919 : Nat := 1297524021978704151491417

theorem tailTrace_2526919 : CollatzResearch.WordTrace tailWord_2526919 prefixEnd_2526919 1297524021978704151491417 := by
  unfold tailWord_2526919
  simp only [CollatzResearch.WordTrace]
  refine ⟨92164307532411501251791811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61442871688274334167861207 92164307532411501251791811)
  ·
    refine ⟨138246461298617251877687717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92164307532411501251791811 138246461298617251877687717)
    ·
      refine ⟨25921211493490734727066447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 138246461298617251877687717 25921211493490734727066447)
      ·
        refine ⟨38881817240236102090599671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25921211493490734727066447 38881817240236102090599671)
        ·
          refine ⟨58322725860354153135899507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38881817240236102090599671 58322725860354153135899507)
          ·
            refine ⟨87484088790531229703849261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58322725860354153135899507 87484088790531229703849261)
            ·
              refine ⟨32806533296449211138943473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87484088790531229703849261 32806533296449211138943473)
              ·
                refine ⟨24604899972336908354207605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32806533296449211138943473 24604899972336908354207605)
                ·
                  refine ⟨2306709372406585158206963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24604899972336908354207605 2306709372406585158206963)
                  ·
                    refine ⟨3460064058609877737310445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2306709372406585158206963 3460064058609877737310445)
                    ·
                      refine ⟨1297524021978704151491417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3460064058609877737310445 1297524021978704151491417)
                      ·
                        rfl

theorem cell23_2526919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 5, 1, 3].length) (baseStart_2526919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2526919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2526919 prefixEnd_2526919 := by exact prefixLift 2526919
  have htrace : WordTrace (prefixWord ++ tailWord_2526919) baseStart_2526919 baseEnd_2526919 := by
    simpa [prefixWord, tailWord_2526919, baseEnd_2526919] using wordTrace_append hprefix tailTrace_2526919
  have hstable : (prefixWord ++ tailWord_2526919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526919).length < 2 ^ (prefixWord ++ tailWord_2526919).sum := by decide
  have hdescent : baseEnd_2526919 < baseStart_2526919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526936 : List Nat := [2, 1, 2, 2, 3, 1, 4, 1, 3, 1, 3]
def baseStart_2526936 : Nat := 118140960795 + 2526936 * 2 ^ 59
def prefixEnd_2526936 : Nat := 4983230072969 + 3 ^ 40 * 2526936 * 2
def baseEnd_2526936 : Nat := 1297532751149830584978839

theorem tailTrace_2526936 : CollatzResearch.WordTrace tailWord_2526936 prefixEnd_2526936 1297532751149830584978839 := by
  unfold tailWord_2526936
  simp only [CollatzResearch.WordTrace]
  refine ⟨46082463786674956577580331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61443285048899942103440441 46082463786674956577580331)
  ·
    refine ⟨69123695680012434866370497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46082463786674956577580331 69123695680012434866370497)
    ·
      refine ⟨51842771760009326149777873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69123695680012434866370497 51842771760009326149777873)
      ·
        refine ⟨38882078820006994612333405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51842771760009326149777873 38882078820006994612333405)
        ·
          refine ⟨14580779557502622979625027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38882078820006994612333405 14580779557502622979625027)
          ·
            refine ⟨21871169336253934469437541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14580779557502622979625027 21871169336253934469437541)
            ·
              refine ⟨4100844250547612713019539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21871169336253934469437541 4100844250547612713019539)
              ·
                refine ⟨6151266375821419069529309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4100844250547612713019539 6151266375821419069529309)
                ·
                  refine ⟨2306724890933032151073491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6151266375821419069529309 2306724890933032151073491)
                  ·
                    refine ⟨3460087336399548226610237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2306724890933032151073491 3460087336399548226610237)
                    ·
                      refine ⟨1297532751149830584978839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3460087336399548226610237 1297532751149830584978839)
                      ·
                        rfl

theorem cell23_2526936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 1, 3, 1, 3].length) (baseStart_2526936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2526936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2526936 prefixEnd_2526936 := by exact prefixLift 2526936
  have htrace : WordTrace (prefixWord ++ tailWord_2526936) baseStart_2526936 baseEnd_2526936 := by
    simpa [prefixWord, tailWord_2526936, baseEnd_2526936] using wordTrace_append hprefix tailTrace_2526936
  have hstable : (prefixWord ++ tailWord_2526936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526936).length < 2 ^ (prefixWord ++ tailWord_2526936).sum := by decide
  have hdescent : baseEnd_2526936 < baseStart_2526936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526959 : List Nat := [1, 1, 2, 1, 5, 1, 1, 1, 2, 6, 2]
def baseStart_2526959 : Nat := 118140960795 + 2526959 * 2 ^ 59
def prefixEnd_2526959 : Nat := 4983230072969 + 3 ^ 40 * 2526959 * 2
def baseEnd_2526959 : Nat := 1297544561204883994991233

theorem tailTrace_2526959 : CollatzResearch.WordTrace tailWord_2526959 prefixEnd_2526959 1297544561204883994991233 := by
  unfold tailWord_2526959
  simp only [CollatzResearch.WordTrace]
  refine ⟨92165766452266588083247931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61443844301511058722165287 92165766452266588083247931)
  ·
    refine ⟨138248649678399882124871897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92165766452266588083247931 138248649678399882124871897)
    ·
      refine ⟨103686487258799911593653923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138248649678399882124871897 103686487258799911593653923)
      ·
        refine ⟨155529730888199867390480885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103686487258799911593653923 155529730888199867390480885)
        ·
          refine ⟨14580912270768737567857583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 155529730888199867390480885 14580912270768737567857583)
          ·
            refine ⟨21871368406153106351786375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14580912270768737567857583 21871368406153106351786375)
            ·
              refine ⟨32807052609229659527679563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21871368406153106351786375 32807052609229659527679563)
              ·
                refine ⟨49210578913844489291519345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32807052609229659527679563 49210578913844489291519345)
                ·
                  refine ⟨36907934185383366968639509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49210578913844489291519345 36907934185383366968639509)
                  ·
                    refine ⟨1730059414939845326654977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 36907934185383366968639509 1730059414939845326654977)
                    ·
                      refine ⟨1297544561204883994991233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1730059414939845326654977 1297544561204883994991233)
                      ·
                        rfl

theorem cell23_2526959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 6, 2].length) (baseStart_2526959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2526959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2526959 prefixEnd_2526959 := by exact prefixLift 2526959
  have htrace : WordTrace (prefixWord ++ tailWord_2526959) baseStart_2526959 baseEnd_2526959 := by
    simpa [prefixWord, tailWord_2526959, baseEnd_2526959] using wordTrace_append hprefix tailTrace_2526959
  have hstable : (prefixWord ++ tailWord_2526959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526959).length < 2 ^ (prefixWord ++ tailWord_2526959).sum := by decide
  have hdescent : baseEnd_2526959 < baseStart_2526959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526999 : List Nat := [1, 1, 3, 4, 2, 2, 2, 8]
def baseStart_2526999 : Nat := 118140960795 + 2526999 * 2 ^ 59
def prefixEnd_2526999 : Nat := 4983230072969 + 3 ^ 40 * 2526999 * 2
def baseEnd_2526999 : Nat := 48057966682631994018187

theorem tailTrace_2526999 : CollatzResearch.WordTrace tailWord_2526999 prefixEnd_2526999 48057966682631994018187 := by
  unfold tailWord_2526999
  simp only [CollatzResearch.WordTrace]
  refine ⟨92167225372121674914704051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61444816914747783276469367 92167225372121674914704051)
  ·
    refine ⟨138250838058182512372056077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92167225372121674914704051 138250838058182512372056077)
    ·
      refine ⟨51844064271818442139521029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138250838058182512372056077 51844064271818442139521029)
      ·
        refine ⟨9720762050965957901160193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51844064271818442139521029 9720762050965957901160193)
        ·
          refine ⟨7290571538224468425870145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9720762050965957901160193 7290571538224468425870145)
          ·
            refine ⟨5467928653668351319402609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7290571538224468425870145 5467928653668351319402609)
            ·
              refine ⟨4100946490251263489551957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5467928653668351319402609 4100946490251263489551957)
              ·
                refine ⟨48057966682631994018187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4100946490251263489551957 48057966682631994018187)
                ·
                  rfl

theorem cell23_2526999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 8].length) (baseStart_2526999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2526999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2526999 prefixEnd_2526999 := by exact prefixLift 2526999
  have htrace : WordTrace (prefixWord ++ tailWord_2526999) baseStart_2526999 baseEnd_2526999 := by
    simpa [prefixWord, tailWord_2526999, baseEnd_2526999] using wordTrace_append hprefix tailTrace_2526999
  have hstable : (prefixWord ++ tailWord_2526999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526999).length < 2 ^ (prefixWord ++ tailWord_2526999).sum := by decide
  have hdescent : baseEnd_2526999 < baseStart_2526999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527013 : List Nat := [1, 3, 1, 2, 3, 4, 1, 2, 1, 2, 3]
def baseStart_2527013 : Nat := 118140960795 + 2527013 * 2 ^ 59
def prefixEnd_2527013 : Nat := 4983230072969 + 3 ^ 40 * 2527013 * 2
def baseEnd_2527013 : Nat := 1297572289160226783715985

theorem tailTrace_2527013 : CollatzResearch.WordTrace tailWord_2527013 prefixEnd_2527013 1297572289160226783715985 := by
  unfold tailWord_2527013
  simp only [CollatzResearch.WordTrace]
  refine ⟨92167735994070955305713693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61445157329380636870475795 92167735994070955305713693)
  ·
    refine ⟨34562900997776608239642635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92167735994070955305713693 34562900997776608239642635)
    ·
      refine ⟨51844351496664912359463953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34562900997776608239642635 51844351496664912359463953)
      ·
        refine ⟨38883263622498684269597965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51844351496664912359463953 38883263622498684269597965)
        ·
          refine ⟨14581223858437006601099237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38883263622498684269597965 14581223858437006601099237)
          ·
            refine ⟨2733979473456938737706107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14581223858437006601099237 2733979473456938737706107)
            ·
              refine ⟨4100969210185408106559161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2733979473456938737706107 4100969210185408106559161)
              ·
                refine ⟨3075726907639056079919371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4100969210185408106559161 3075726907639056079919371)
                ·
                  refine ⟨4613590361458584119879057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3075726907639056079919371 4613590361458584119879057)
                  ·
                    refine ⟨3460192771093938089909293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4613590361458584119879057 3460192771093938089909293)
                    ·
                      refine ⟨1297572289160226783715985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3460192771093938089909293 1297572289160226783715985)
                      ·
                        rfl

theorem cell23_2527013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 2, 1, 2, 3].length) (baseStart_2527013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2527013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2527013 prefixEnd_2527013 := by exact prefixLift 2527013
  have htrace : WordTrace (prefixWord ++ tailWord_2527013) baseStart_2527013 baseEnd_2527013 := by
    simpa [prefixWord, tailWord_2527013, baseEnd_2527013] using wordTrace_append hprefix tailTrace_2527013
  have hstable : (prefixWord ++ tailWord_2527013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527013).length < 2 ^ (prefixWord ++ tailWord_2527013).sum := by decide
  have hdescent : baseEnd_2527013 < baseStart_2527013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527026 : List Nat := [3, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3]
def baseStart_2527026 : Nat := 118140960795 + 2527026 * 2 ^ 59
def prefixEnd_2527026 : Nat := 4983230072969 + 3 ^ 40 * 2527026 * 2
def baseEnd_2527026 : Nat := 1297578964408735232853425

theorem tailTrace_2527026 : CollatzResearch.WordTrace tailWord_2527026 prefixEnd_2527026 1297578964408735232853425 := by
  unfold tailWord_2527026
  simp only [CollatzResearch.WordTrace]
  refine ⟨23042052535755964631484233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61445473428682572350624621 23042052535755964631484233)
  ·
    refine ⟨17281539401816973473613175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23042052535755964631484233 17281539401816973473613175)
    ·
      refine ⟨25922309102725460210419763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17281539401816973473613175 25922309102725460210419763)
      ·
        refine ⟨38883463654088190315629645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25922309102725460210419763 38883463654088190315629645)
        ·
          refine ⟨14581298870283071368361117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38883463654088190315629645 14581298870283071368361117)
          ·
            refine ⟨5467987076356151763135419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14581298870283071368361117 5467987076356151763135419)
            ·
              refine ⟨8201980614534227644703129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5467987076356151763135419 8201980614534227644703129)
              ·
                refine ⟨6151485460900670733527347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8201980614534227644703129 6151485460900670733527347)
                ·
                  refine ⟨9227228191351006100291021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6151485460900670733527347 9227228191351006100291021)
                  ·
                    refine ⟨3460210571756627287609133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9227228191351006100291021 3460210571756627287609133)
                    ·
                      refine ⟨1297578964408735232853425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3460210571756627287609133 1297578964408735232853425)
                      ·
                        rfl

theorem cell23_2527026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3].length) (baseStart_2527026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2527026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2527026 prefixEnd_2527026 := by exact prefixLift 2527026
  have htrace : WordTrace (prefixWord ++ tailWord_2527026) baseStart_2527026 baseEnd_2527026 := by
    simpa [prefixWord, tailWord_2527026, baseEnd_2527026] using wordTrace_append hprefix tailTrace_2527026
  have hstable : (prefixWord ++ tailWord_2527026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527026).length < 2 ^ (prefixWord ++ tailWord_2527026).sum := by decide
  have hdescent : baseEnd_2527026 < baseStart_2527026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527043 : List Nat := [1, 1, 1, 3, 1, 6, 2, 2, 2, 1, 3]
def baseStart_2527043 : Nat := 118140960795 + 2527043 * 2 ^ 59
def prefixEnd_2527043 : Nat := 4983230072969 + 3 ^ 40 * 2527043 * 2
def baseEnd_2527043 : Nat := 1297587693579861666340847

theorem tailTrace_2527043 : CollatzResearch.WordTrace tailWord_2527043 prefixEnd_2527043 1297587693579861666340847 := by
  unfold tailWord_2527043
  simp only [CollatzResearch.WordTrace]
  refine ⟨92168830183962270429305783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61445886789308180286203855 92168830183962270429305783)
  ·
    refine ⟨138253245275943405643958675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92168830183962270429305783 138253245275943405643958675)
    ·
      refine ⟨207379867913915108465938013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138253245275943405643958675 207379867913915108465938013)
      ·
        refine ⟨77767450467718165674726755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 207379867913915108465938013 77767450467718165674726755)
        ·
          refine ⟨116651175701577248512090133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77767450467718165674726755 116651175701577248512090133)
          ·
            refine ⟨5468023861011433524004225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 116651175701577248512090133 5468023861011433524004225)
            ·
              refine ⟨4101017895758575143003169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5468023861011433524004225 4101017895758575143003169)
              ·
                refine ⟨3075763421818931357252377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4101017895758575143003169 3075763421818931357252377)
                ·
                  refine ⟨2306822566364198517939283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3075763421818931357252377 2306822566364198517939283)
                  ·
                    refine ⟨3460233849546297776908925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2306822566364198517939283 3460233849546297776908925)
                    ·
                      refine ⟨1297587693579861666340847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3460233849546297776908925 1297587693579861666340847)
                      ·
                        rfl

theorem cell23_2527043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 2, 2, 1, 3].length) (baseStart_2527043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2527043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2527043 prefixEnd_2527043 := by exact prefixLift 2527043
  have htrace : WordTrace (prefixWord ++ tailWord_2527043) baseStart_2527043 baseEnd_2527043 := by
    simpa [prefixWord, tailWord_2527043, baseEnd_2527043] using wordTrace_append hprefix tailTrace_2527043
  have hstable : (prefixWord ++ tailWord_2527043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527043).length < 2 ^ (prefixWord ++ tailWord_2527043).sum := by decide
  have hdescent : baseEnd_2527043 < baseStart_2527043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527079 : List Nat := [1, 1, 5, 1, 2, 1, 1, 2, 1, 4, 4]
def baseStart_2527079 : Nat := 118140960795 + 2527079 * 2 ^ 59
def prefixEnd_2527079 : Nat := 4983230072969 + 3 ^ 40 * 2527079 * 2
def baseEnd_2527079 : Nat := 1297606178883423525490681

theorem tailTrace_2527079 : CollatzResearch.WordTrace tailWord_2527079 prefixEnd_2527079 1297606178883423525490681 := by
  unfold tailWord_2527079
  simp only [CollatzResearch.WordTrace]
  refine ⟨92170143211831848577616291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61446762141221232385077527 92170143211831848577616291)
  ·
    refine ⟨138255214817747772866424437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92170143211831848577616291 138255214817747772866424437)
    ·
      refine ⟨12961426389163853706227291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 138255214817747772866424437 12961426389163853706227291)
      ·
        refine ⟨19442139583745780559340937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12961426389163853706227291 19442139583745780559340937)
        ·
          refine ⟨14581604687809335419505703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19442139583745780559340937 14581604687809335419505703)
          ·
            refine ⟨21872407031714003129258555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14581604687809335419505703 21872407031714003129258555)
            ·
              refine ⟨32808610547571004693887833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21872407031714003129258555 32808610547571004693887833)
              ·
                refine ⟨24606457910678253520415875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32808610547571004693887833 24606457910678253520415875)
                ·
                  refine ⟨36909686866017380280623813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24606457910678253520415875 36909686866017380280623813)
                  ·
                    refine ⟨6920566287378258802616965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36909686866017380280623813 6920566287378258802616965)
                    ·
                      refine ⟨1297606178883423525490681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6920566287378258802616965 1297606178883423525490681)
                      ·
                        rfl

theorem cell23_2527079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_2527079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2527079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2527079 prefixEnd_2527079 := by exact prefixLift 2527079
  have htrace : WordTrace (prefixWord ++ tailWord_2527079) baseStart_2527079 baseEnd_2527079 := by
    simpa [prefixWord, tailWord_2527079, baseEnd_2527079] using wordTrace_append hprefix tailTrace_2527079
  have hstable : (prefixWord ++ tailWord_2527079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527079).length < 2 ^ (prefixWord ++ tailWord_2527079).sum := by decide
  have hdescent : baseEnd_2527079 < baseStart_2527079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527094 : List Nat := [5, 1, 1, 3, 3, 1, 1, 2, 2, 1, 3]
def baseStart_2527094 : Nat := 118140960795 + 2527094 * 2 ^ 59
def prefixEnd_2527094 : Nat := 4983230072969 + 3 ^ 40 * 2527094 * 2
def baseEnd_2527094 : Nat := 1297613881093240966803113

theorem tailTrace_2527094 : CollatzResearch.WordTrace tailWord_2527094 prefixEnd_2527094 1297613881093240966803113 := by
  unfold tailWord_2527094
  simp only [CollatzResearch.WordTrace]
  refine ⟨5760668144173594133713271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61447126871185004092941557 5760668144173594133713271)
  ·
    refine ⟨8641002216260391200569907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5760668144173594133713271 8641002216260391200569907)
    ·
      refine ⟨12961503324390586800854861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8641002216260391200569907 12961503324390586800854861)
      ·
        refine ⟨4860563746646470050320573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12961503324390586800854861 4860563746646470050320573)
        ·
          refine ⟨1822711404992426268870215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4860563746646470050320573 1822711404992426268870215)
          ·
            refine ⟨2734067107488639403305323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1822711404992426268870215 2734067107488639403305323)
            ·
              refine ⟨4101100661232959104957985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2734067107488639403305323 4101100661232959104957985)
              ·
                refine ⟨3075825495924719328718489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4101100661232959104957985 3075825495924719328718489)
                ·
                  refine ⟨2306869121943539496538867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3075825495924719328718489 2306869121943539496538867)
                  ·
                    refine ⟨3460303682915309244808301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2306869121943539496538867 3460303682915309244808301)
                    ·
                      refine ⟨1297613881093240966803113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3460303682915309244808301 1297613881093240966803113)
                      ·
                        rfl

theorem cell23_2527094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_2527094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2527094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2527094 prefixEnd_2527094 := by exact prefixLift 2527094
  have htrace : WordTrace (prefixWord ++ tailWord_2527094) baseStart_2527094 baseEnd_2527094 := by
    simpa [prefixWord, tailWord_2527094, baseEnd_2527094] using wordTrace_append hprefix tailTrace_2527094
  have hstable : (prefixWord ++ tailWord_2527094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527094).length < 2 ^ (prefixWord ++ tailWord_2527094).sum := by decide
  have hdescent : baseEnd_2527094 < baseStart_2527094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527219 : List Nat := [1, 1, 1, 2, 2, 2, 1, 2, 2, 4, 5]
def baseStart_2527219 : Nat := 118140960795 + 2527219 * 2 ^ 59
def prefixEnd_2527219 : Nat := 4983230072969 + 3 ^ 40 * 2527219 * 2
def baseEnd_2527219 : Nat := 1297678066175052977740037

theorem tailTrace_2527219 : CollatzResearch.WordTrace tailWord_2527219 prefixEnd_2527219 1297678066175052977740037 := by
  unfold tailWord_2527219
  simp only [CollatzResearch.WordTrace]
  refine ⟨92175249431324652487712711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61450166287549768325141807 92175249431324652487712711)
  ·
    refine ⟨138262874146986978731569067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92175249431324652487712711 138262874146986978731569067)
    ·
      refine ⟨207394311220480468097353601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138262874146986978731569067 207394311220480468097353601)
      ·
        refine ⟨155545733415360351073015201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207394311220480468097353601 155545733415360351073015201)
        ·
          refine ⟨116659300061520263304761401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155545733415360351073015201 116659300061520263304761401)
          ·
            refine ⟨87494475046140197478571051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116659300061520263304761401 87494475046140197478571051)
            ·
              refine ⟨131241712569210296217856577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87494475046140197478571051 131241712569210296217856577)
              ·
                refine ⟨98431284426907722163392433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131241712569210296217856577 98431284426907722163392433)
                ·
                  refine ⟨73823463320180791622544325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98431284426907722163392433 73823463320180791622544325)
                  ·
                    refine ⟨13841899372533898429227061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 73823463320180791622544325 13841899372533898429227061)
                    ·
                      refine ⟨1297678066175052977740037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13841899372533898429227061 1297678066175052977740037)
                      ·
                        rfl

theorem cell23_2527219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4, 5].length) (baseStart_2527219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2527219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2527219 prefixEnd_2527219 := by exact prefixLift 2527219
  have htrace : WordTrace (prefixWord ++ tailWord_2527219) baseStart_2527219 baseEnd_2527219 := by
    simpa [prefixWord, tailWord_2527219, baseEnd_2527219] using wordTrace_append hprefix tailTrace_2527219
  have hstable : (prefixWord ++ tailWord_2527219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527219).length < 2 ^ (prefixWord ++ tailWord_2527219).sum := by decide
  have hdescent : baseEnd_2527219 < baseStart_2527219 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527233 : List Nat := [1, 2, 4, 1, 2, 1, 2, 2, 1, 5, 2]
def baseStart_2527233 : Nat := 118140960795 + 2527233 * 2 ^ 59
def prefixEnd_2527233 : Nat := 4983230072969 + 3 ^ 40 * 2527233 * 2
def baseEnd_2527233 : Nat := 1297685254904215922964973

theorem tailTrace_2527233 : CollatzResearch.WordTrace tailWord_2527233 prefixEnd_2527233 1297685254904215922964973 := by
  unfold tailWord_2527233
  simp only [CollatzResearch.WordTrace]
  refine ⟨92175760053273932878722353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61450506702182621919148235 92175760053273932878722353)
  ·
    refine ⟨69131820039955449659041765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92175760053273932878722353 69131820039955449659041765)
    ·
      refine ⟨12962216257491646811070331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69131820039955449659041765 12962216257491646811070331)
      ·
        refine ⟨19443324386237470216605497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12962216257491646811070331 19443324386237470216605497)
        ·
          refine ⟨14582493289678102662454123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19443324386237470216605497 14582493289678102662454123)
          ·
            refine ⟨21873739934517153993681185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14582493289678102662454123 21873739934517153993681185)
            ·
              refine ⟨16405304950887865495260889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21873739934517153993681185 16405304950887865495260889)
              ·
                refine ⟨12303978713165899121445667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16405304950887865495260889 12303978713165899121445667)
                ·
                  refine ⟨18455968069748848682168501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12303978713165899121445667 18455968069748848682168501)
                  ·
                    refine ⟨1730247006538954563953297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18455968069748848682168501 1730247006538954563953297)
                    ·
                      refine ⟨1297685254904215922964973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1730247006538954563953297 1297685254904215922964973)
                      ·
                        rfl

theorem cell23_2527233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 5, 2].length) (baseStart_2527233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2527233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2527233 prefixEnd_2527233 := by exact prefixLift 2527233
  have htrace : WordTrace (prefixWord ++ tailWord_2527233) baseStart_2527233 baseEnd_2527233 := by
    simpa [prefixWord, tailWord_2527233, baseEnd_2527233] using wordTrace_append hprefix tailTrace_2527233
  have hstable : (prefixWord ++ tailWord_2527233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527233).length < 2 ^ (prefixWord ++ tailWord_2527233).sum := by decide
  have hdescent : baseEnd_2527233 < baseStart_2527233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527256 : List Nat := [2, 1, 2, 3, 2, 1, 1, 4, 1, 6]
def baseStart_2527256 : Nat := 118140960795 + 2527256 * 2 ^ 59
def prefixEnd_2527256 : Nat := 4983230072969 + 3 ^ 40 * 2527256 * 2
def baseEnd_2527256 : Nat := 432565688319756444325789

theorem tailTrace_2527256 : CollatzResearch.WordTrace tailWord_2527256 prefixEnd_2527256 432565688319756444325789 := by
  unfold tailWord_2527256
  simp only [CollatzResearch.WordTrace]
  refine ⟨46088299466095303903404811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61451065954793738537873081 46088299466095303903404811)
  ·
    refine ⟨69132449199142955855107217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46088299466095303903404811 69132449199142955855107217)
    ·
      refine ⟨51849336899357216891330413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69132449199142955855107217 51849336899357216891330413)
      ·
        refine ⟨19443501337258956334248905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51849336899357216891330413 19443501337258956334248905)
        ·
          refine ⟨14582626002944217250686679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19443501337258956334248905 14582626002944217250686679)
          ·
            refine ⟨21873939004416325876030019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14582626002944217250686679 21873939004416325876030019)
            ·
              refine ⟨32810908506624488814045029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21873939004416325876030019 32810908506624488814045029)
              ·
                refine ⟨6152045344992091652633443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32810908506624488814045029 6152045344992091652633443)
                ·
                  refine ⟨9228068017488137478950165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6152045344992091652633443 9228068017488137478950165)
                  ·
                    refine ⟨432565688319756444325789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9228068017488137478950165 432565688319756444325789)
                    ·
                      rfl

theorem cell23_2527256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 4, 1, 6].length) (baseStart_2527256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2527256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2527256 prefixEnd_2527256 := by exact prefixLift 2527256
  have htrace : WordTrace (prefixWord ++ tailWord_2527256) baseStart_2527256 baseEnd_2527256 := by
    simpa [prefixWord, tailWord_2527256, baseEnd_2527256] using wordTrace_append hprefix tailTrace_2527256
  have hstable : (prefixWord ++ tailWord_2527256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527256).length < 2 ^ (prefixWord ++ tailWord_2527256).sum := by decide
  have hdescent : baseEnd_2527256 < baseStart_2527256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527260 : List Nat := [2, 2, 3, 1, 3, 1, 4, 1, 1, 5]
def baseStart_2527260 : Nat := 118140960795 + 2527260 * 2 ^ 59
def prefixEnd_2527260 : Nat := 4983230072969 + 3 ^ 40 * 2527260 * 2
def baseEnd_2527260 : Nat := 432566372960629105775783

theorem tailTrace_2527260 : CollatzResearch.WordTrace tailWord_2527260 prefixEnd_2527260 432566372960629105775783 := by
  unfold tailWord_2527260
  simp only [CollatzResearch.WordTrace]
  refine ⟨46088372412088058244977617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61451163216117410993303489 46088372412088058244977617)
  ·
    refine ⟨34566279309066043683733213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46088372412088058244977617 34566279309066043683733213)
    ·
      refine ⟨12962354740899766381399955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34566279309066043683733213 12962354740899766381399955)
      ·
        refine ⟨19443532111349649572099933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12962354740899766381399955 19443532111349649572099933)
        ·
          refine ⟨7291324541756118589537475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19443532111349649572099933 7291324541756118589537475)
          ·
            refine ⟨10936986812634177884306213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7291324541756118589537475 10936986812634177884306213)
            ·
              refine ⟨2050685027368908353307415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10936986812634177884306213 2050685027368908353307415)
              ·
                refine ⟨3076027541053362529961123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2050685027368908353307415 3076027541053362529961123)
                ·
                  refine ⟨4614041311580043794941685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3076027541053362529961123 4614041311580043794941685)
                  ·
                    refine ⟨432566372960629105775783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4614041311580043794941685 432566372960629105775783)
                    ·
                      rfl

theorem cell23_2527260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4, 1, 1, 5].length) (baseStart_2527260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2527260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2527260 prefixEnd_2527260 := by exact prefixLift 2527260
  have htrace : WordTrace (prefixWord ++ tailWord_2527260) baseStart_2527260 baseEnd_2527260 := by
    simpa [prefixWord, tailWord_2527260, baseEnd_2527260] using wordTrace_append hprefix tailTrace_2527260
  have hstable : (prefixWord ++ tailWord_2527260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527260).length < 2 ^ (prefixWord ++ tailWord_2527260).sum := by decide
  have hdescent : baseEnd_2527260 < baseStart_2527260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527263 : List Nat := [1, 1, 2, 4, 1, 2, 3, 3, 1, 1, 4]
def baseStart_2527263 : Nat := 118140960795 + 2527263 * 2 ^ 59
def prefixEnd_2527263 : Nat := 4983230072969 + 3 ^ 40 * 2527263 * 2
def baseEnd_2527263 : Nat := 1297700659323850805589835

theorem tailTrace_2527263 : CollatzResearch.WordTrace tailWord_2527263 prefixEnd_2527263 1297700659323850805589835 := by
  unfold tailWord_2527263
  simp only [CollatzResearch.WordTrace]
  refine ⟨92176854243165248002314443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61451236162110165334876295 92176854243165248002314443)
  ·
    refine ⟨138265281364747872003471665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92176854243165248002314443 138265281364747872003471665)
    ·
      refine ⟨103698961023560904002603749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138265281364747872003471665 103698961023560904002603749)
      ·
        refine ⟨19443555191917669500488203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103698961023560904002603749 19443555191917669500488203)
        ·
          refine ⟨29165332787876504250732305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19443555191917669500488203 29165332787876504250732305)
          ·
            refine ⟨21873999590907378188049229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29165332787876504250732305 21873999590907378188049229)
            ·
              refine ⟨8202749846590266820518461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21873999590907378188049229 8202749846590266820518461)
              ·
                refine ⟨3076031192471350057694423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8202749846590266820518461 3076031192471350057694423)
                ·
                  refine ⟨4614046788707025086541635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3076031192471350057694423 4614046788707025086541635)
                  ·
                    refine ⟨6921070183060537629812453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4614046788707025086541635 6921070183060537629812453)
                    ·
                      refine ⟨1297700659323850805589835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6921070183060537629812453 1297700659323850805589835)
                      ·
                        rfl

theorem cell23_2527263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 3, 1, 1, 4].length) (baseStart_2527263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2527263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2527263 prefixEnd_2527263 := by exact prefixLift 2527263
  have htrace : WordTrace (prefixWord ++ tailWord_2527263) baseStart_2527263 baseEnd_2527263 := by
    simpa [prefixWord, tailWord_2527263, baseEnd_2527263] using wordTrace_append hprefix tailTrace_2527263
  have hstable : (prefixWord ++ tailWord_2527263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527263).length < 2 ^ (prefixWord ++ tailWord_2527263).sum := by decide
  have hdescent : baseEnd_2527263 < baseStart_2527263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527280 : List Nat := [2, 1, 1, 1, 2, 5, 1, 3, 3, 2, 2]
def baseStart_2527280 : Nat := 118140960795 + 2527280 * 2 ^ 59
def prefixEnd_2527280 : Nat := 4983230072969 + 3 ^ 40 * 2527280 * 2
def baseEnd_2527280 : Nat := 1297709388494977239077257

theorem tailTrace_2527280 : CollatzResearch.WordTrace tailWord_2527280 prefixEnd_2527280 1297709388494977239077257 := by
  unfold tailWord_2527280
  simp only [CollatzResearch.WordTrace]
  refine ⟨46088737142051829952841647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61451649522735773270455529 46088737142051829952841647)
  ·
    refine ⟨69133105713077744929262471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46088737142051829952841647 69133105713077744929262471)
    ·
      refine ⟨103699658569616617393893707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69133105713077744929262471 103699658569616617393893707)
      ·
        refine ⟨155549487854424926090840561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103699658569616617393893707 155549487854424926090840561)
        ·
          refine ⟨116662115890818694568130421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155549487854424926090840561 116662115890818694568130421)
          ·
            refine ⟨10937073364764252615762227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 116662115890818694568130421 10937073364764252615762227)
            ·
              refine ⟨16405610047146378923643341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10937073364764252615762227 16405610047146378923643341)
              ·
                refine ⟨6152103767679892096366253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16405610047146378923643341 6152103767679892096366253)
                ·
                  refine ⟨2307038912879959536137345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6152103767679892096366253 2307038912879959536137345)
                  ·
                    refine ⟨1730279184659969652103009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2307038912879959536137345 1730279184659969652103009)
                    ·
                      refine ⟨1297709388494977239077257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1730279184659969652103009 1297709388494977239077257)
                      ·
                        rfl

theorem cell23_2527280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 3, 3, 2, 2].length) (baseStart_2527280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2527280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2527280 prefixEnd_2527280 := by exact prefixLift 2527280
  have htrace : WordTrace (prefixWord ++ tailWord_2527280) baseStart_2527280 baseEnd_2527280 := by
    simpa [prefixWord, tailWord_2527280, baseEnd_2527280] using wordTrace_append hprefix tailTrace_2527280
  have hstable : (prefixWord ++ tailWord_2527280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527280).length < 2 ^ (prefixWord ++ tailWord_2527280).sum := by decide
  have hdescent : baseEnd_2527280 < baseStart_2527280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527297 : List Nat := [1, 2, 5, 1, 2, 1, 2, 2, 3, 2, 2]
def baseStart_2527297 : Nat := 118140960795 + 2527297 * 2 ^ 59
def prefixEnd_2527297 : Nat := 4983230072969 + 3 ^ 40 * 2527297 * 2
def baseEnd_2527297 : Nat := 1297718117666103672564679

theorem tailTrace_2527297 : CollatzResearch.WordTrace tailWord_2527297 prefixEnd_2527297 1297718117666103672564679 := by
  unfold tailWord_2527297
  simp only [CollatzResearch.WordTrace]
  refine ⟨92178094325042071809052145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61452062883361381206034763 92178094325042071809052145)
  ·
    refine ⟨69133570743781553856789109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92178094325042071809052145 69133570743781553856789109)
    ·
      refine ⟨6481272257229520674073979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 69133570743781553856789109 6481272257229520674073979)
      ·
        refine ⟨9721908385844281011110969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6481272257229520674073979 9721908385844281011110969)
        ·
          refine ⟨7291431289383210758333227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9721908385844281011110969 7291431289383210758333227)
          ·
            refine ⟨10937146934074816137499841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7291431289383210758333227 10937146934074816137499841)
            ·
              refine ⟨8202860200556112103124881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10937146934074816137499841 8202860200556112103124881)
              ·
                refine ⟨6152145150417084077343661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8202860200556112103124881 6152145150417084077343661)
                ·
                  refine ⟨2307054431406406529003873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6152145150417084077343661 2307054431406406529003873)
                  ·
                    refine ⟨1730290823554804896752905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2307054431406406529003873 1730290823554804896752905)
                    ·
                      refine ⟨1297718117666103672564679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1730290823554804896752905 1297718117666103672564679)
                      ·
                        rfl

theorem cell23_2527297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_2527297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2527297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2527297 prefixEnd_2527297 := by exact prefixLift 2527297
  have htrace : WordTrace (prefixWord ++ tailWord_2527297) baseStart_2527297 baseEnd_2527297 := by
    simpa [prefixWord, tailWord_2527297, baseEnd_2527297] using wordTrace_append hprefix tailTrace_2527297
  have hstable : (prefixWord ++ tailWord_2527297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527297).length < 2 ^ (prefixWord ++ tailWord_2527297).sum := by decide
  have hdescent : baseEnd_2527297 < baseStart_2527297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527316 : List Nat := [2, 4, 1, 1, 1, 1, 1, 2, 1, 9]
def baseStart_2527316 : Nat := 118140960795 + 2527316 * 2 ^ 59
def prefixEnd_2527316 : Nat := 4983230072969 + 3 ^ 40 * 2527316 * 2
def baseEnd_2527316 : Nat := 432575957932846366075697

theorem tailTrace_2527316 : CollatzResearch.WordTrace tailWord_2527316 prefixEnd_2527316 432575957932846366075697 := by
  unfold tailWord_2527316
  simp only [CollatzResearch.WordTrace]
  refine ⟨46089393655986619026996901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61452524874648825369329201 46089393655986619026996901)
  ·
    refine ⟨8641761310497491067561919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46089393655986619026996901 8641761310497491067561919)
    ·
      refine ⟨12962641965746236601342879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8641761310497491067561919 12962641965746236601342879)
      ·
        refine ⟨19443962948619354902014319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12962641965746236601342879 19443962948619354902014319)
        ·
          refine ⟨29165944422929032353021479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19443962948619354902014319 29165944422929032353021479)
          ·
            refine ⟨43748916634393548529532219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29165944422929032353021479 43748916634393548529532219)
            ·
              refine ⟨65623374951590322794298329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43748916634393548529532219 65623374951590322794298329)
              ·
                refine ⟨49217531213692742095723747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65623374951590322794298329 49217531213692742095723747)
                ·
                  refine ⟨73826296820539113143585621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49217531213692742095723747 73826296820539113143585621)
                  ·
                    refine ⟨432575957932846366075697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 73826296820539113143585621 432575957932846366075697)
                    ·
                      rfl

theorem cell23_2527316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_2527316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2527316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2527316 prefixEnd_2527316 := by exact prefixLift 2527316
  have htrace : WordTrace (prefixWord ++ tailWord_2527316) baseStart_2527316 baseEnd_2527316 := by
    simpa [prefixWord, tailWord_2527316, baseEnd_2527316] using wordTrace_append hprefix tailTrace_2527316
  have hstable : (prefixWord ++ tailWord_2527316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527316).length < 2 ^ (prefixWord ++ tailWord_2527316).sum := by decide
  have hdescent : baseEnd_2527316 < baseStart_2527316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527357 : List Nat := [1, 4, 1, 1, 3, 2, 3, 2, 1, 3, 2]
def baseStart_2527357 : Nat := 118140960795 + 2527357 * 2 ^ 59
def prefixEnd_2527357 : Nat := 4983230072969 + 3 ^ 40 * 2527357 * 2
def baseEnd_2527357 : Nat := 1297748926505373437814403

theorem tailTrace_2527357 : CollatzResearch.WordTrace tailWord_2527357 prefixEnd_2527357 1297748926505373437814403 := by
  unfold tailWord_2527357
  simp only [CollatzResearch.WordTrace]
  refine ⟨92180282704824702056236325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61453521803216468037490883 92180282704824702056236325)
  ·
    refine ⟨17283803007154631635544311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92180282704824702056236325 17283803007154631635544311)
    ·
      refine ⟨25925704510731947453316467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17283803007154631635544311 25925704510731947453316467)
      ·
        refine ⟨38888556766097921179974701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25925704510731947453316467 38888556766097921179974701)
        ·
          refine ⟨14583208787286720442490513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38888556766097921179974701 14583208787286720442490513)
          ·
            refine ⟨10937406590465040331867885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14583208787286720442490513 10937406590465040331867885)
            ·
              refine ⟨4101527471424390124450457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10937406590465040331867885 4101527471424390124450457)
              ·
                refine ⟨3076145603568292593337843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4101527471424390124450457 3076145603568292593337843)
                ·
                  refine ⟨4614218405352438890006765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3076145603568292593337843 4614218405352438890006765)
                  ·
                    refine ⟨1730331902007164583752537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4614218405352438890006765 1730331902007164583752537)
                    ·
                      refine ⟨1297748926505373437814403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1730331902007164583752537 1297748926505373437814403)
                      ·
                        rfl

theorem cell23_2527357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 2, 1, 3, 2].length) (baseStart_2527357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2527357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2527357 prefixEnd_2527357 := by exact prefixLift 2527357
  have htrace : WordTrace (prefixWord ++ tailWord_2527357) baseStart_2527357 baseEnd_2527357 := by
    simpa [prefixWord, tailWord_2527357, baseEnd_2527357] using wordTrace_append hprefix tailTrace_2527357
  have hstable : (prefixWord ++ tailWord_2527357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527357).length < 2 ^ (prefixWord ++ tailWord_2527357).sum := by decide
  have hdescent : baseEnd_2527357 < baseStart_2527357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527370 : List Nat := [3, 1, 2, 3, 1, 2, 1, 1, 3, 4, 2]
def baseStart_2527370 : Nat := 118140960795 + 2527370 * 2 ^ 59
def prefixEnd_2527370 : Nat := 4983230072969 + 3 ^ 40 * 2527370 * 2
def baseEnd_2527370 : Nat := 1297755601753881886951843

theorem tailTrace_2527370 : CollatzResearch.WordTrace tailWord_2527370 prefixEnd_2527370 1297755601753881886951843 := by
  unfold tailWord_2527370
  simp only [CollatzResearch.WordTrace]
  refine ⟨23045189213444401319114891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61453837902518403517639709 23045189213444401319114891)
  ·
    refine ⟨34567783820166601978672337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23045189213444401319114891 34567783820166601978672337)
    ·
      refine ⟨25925837865124951484004253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34567783820166601978672337 25925837865124951484004253)
      ·
        refine ⟨9722189199421856806501595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25925837865124951484004253 9722189199421856806501595)
        ·
          refine ⟨14583283799132785209752393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9722189199421856806501595 14583283799132785209752393)
          ·
            refine ⟨10937462849349588907314295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14583283799132785209752393 10937462849349588907314295)
            ·
              refine ⟨16406194274024383360971443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10937462849349588907314295 16406194274024383360971443)
              ·
                refine ⟨24609291411036575041457165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16406194274024383360971443 24609291411036575041457165)
                ·
                  refine ⟨9228484279138715640546437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24609291411036575041457165 9228484279138715640546437)
                  ·
                    refine ⟨1730340802338509182602457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9228484279138715640546437 1730340802338509182602457)
                    ·
                      refine ⟨1297755601753881886951843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1730340802338509182602457 1297755601753881886951843)
                      ·
                        rfl

theorem cell23_2527370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_2527370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2527370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2527370 prefixEnd_2527370 := by exact prefixLift 2527370
  have htrace : WordTrace (prefixWord ++ tailWord_2527370) baseStart_2527370 baseEnd_2527370 := by
    simpa [prefixWord, tailWord_2527370, baseEnd_2527370] using wordTrace_append hprefix tailTrace_2527370
  have hstable : (prefixWord ++ tailWord_2527370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527370).length < 2 ^ (prefixWord ++ tailWord_2527370).sum := by decide
  have hdescent : baseEnd_2527370 < baseStart_2527370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527382 : List Nat := [5, 3, 2, 1, 1, 1, 1, 4, 1, 2, 2]
def baseStart_2527382 : Nat := 118140960795 + 2527382 * 2 ^ 59
def prefixEnd_2527382 : Nat := 4983230072969 + 3 ^ 40 * 2527382 * 2
def baseEnd_2527382 : Nat := 1297761763521735840001789

theorem tailTrace_2527382 : CollatzResearch.WordTrace tailWord_2527382 prefixEnd_2527382 1297761763521735840001789 := by
  unfold tailWord_2527382
  simp only [CollatzResearch.WordTrace]
  refine ⟨5761324658108383207868525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61454129686489420883930933 5761324658108383207868525)
  ·
    refine ⟨2160496746790643702950697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5761324658108383207868525 2160496746790643702950697)
    ·
      refine ⟨1620372560092982777213023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2160496746790643702950697 1620372560092982777213023)
      ·
        refine ⟨2430558840139474165819535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1620372560092982777213023 2430558840139474165819535)
        ·
          refine ⟨3645838260209211248729303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2430558840139474165819535 3645838260209211248729303)
          ·
            refine ⟨5468757390313816873093955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3645838260209211248729303 5468757390313816873093955)
            ·
              refine ⟨8203136085470725309640933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5468757390313816873093955 8203136085470725309640933)
              ·
                refine ⟨1538088016025760995557675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8203136085470725309640933 1538088016025760995557675)
                ·
                  refine ⟨2307132024038641493336513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1538088016025760995557675 2307132024038641493336513)
                  ·
                    refine ⟨1730349018028981120002385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2307132024038641493336513 1730349018028981120002385)
                    ·
                      refine ⟨1297761763521735840001789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1730349018028981120002385 1297761763521735840001789)
                      ·
                        rfl

theorem cell23_2527382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_2527382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2527382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2527382 prefixEnd_2527382 := by exact prefixLift 2527382
  have htrace : WordTrace (prefixWord ++ tailWord_2527382) baseStart_2527382 baseEnd_2527382 := by
    simpa [prefixWord, tailWord_2527382, baseEnd_2527382] using wordTrace_append hprefix tailTrace_2527382
  have hstable : (prefixWord ++ tailWord_2527382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527382).length < 2 ^ (prefixWord ++ tailWord_2527382).sum := by decide
  have hdescent : baseEnd_2527382 < baseStart_2527382 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527517 : List Nat := [1, 4, 2, 3, 2, 1, 1, 3, 6]
def baseStart_2527517 : Nat := 118140960795 + 2527517 * 2 ^ 59
def prefixEnd_2527517 : Nat := 4983230072969 + 3 ^ 40 * 2527517 * 2
def baseEnd_2527517 : Nat := 144203453712232534645963

theorem tailTrace_2527517 : CollatzResearch.WordTrace tailWord_2527517 prefixEnd_2527517 144203453712232534645963 := by
  unfold tailWord_2527517
  simp only [CollatzResearch.WordTrace]
  refine ⟨92186118384245049382060805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61457412256163366254707203 92186118384245049382060805)
  ·
    refine ⟨17284897197045946759136401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92186118384245049382060805 17284897197045946759136401)
    ·
      refine ⟨12963672897784460069352301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17284897197045946759136401 12963672897784460069352301)
      ·
        refine ⟨4861377336669172526007113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12963672897784460069352301 4861377336669172526007113)
        ·
          refine ⟨3646033002501879394505335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4861377336669172526007113 3646033002501879394505335)
          ·
            refine ⟨5469049503752819091758003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3646033002501879394505335 5469049503752819091758003)
            ·
              refine ⟨8203574255629228637637005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5469049503752819091758003 8203574255629228637637005)
              ·
                refine ⟨3076340345860960739113877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8203574255629228637637005 3076340345860960739113877)
                ·
                  refine ⟨144203453712232534645963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3076340345860960739113877 144203453712232534645963)
                  ·
                    rfl

theorem cell23_2527517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 3, 6].length) (baseStart_2527517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2527517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2527517 prefixEnd_2527517 := by exact prefixLift 2527517
  have htrace : WordTrace (prefixWord ++ tailWord_2527517) baseStart_2527517 baseEnd_2527517 := by
    simpa [prefixWord, tailWord_2527517, baseEnd_2527517] using wordTrace_append hprefix tailTrace_2527517
  have hstable : (prefixWord ++ tailWord_2527517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527517).length < 2 ^ (prefixWord ++ tailWord_2527517).sum := by decide
  have hdescent : baseEnd_2527517 < baseStart_2527517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527560 : List Nat := [2, 1, 3, 1, 1, 2, 2, 3, 4, 4]
def baseStart_2527560 : Nat := 118140960795 + 2527560 * 2 ^ 59
def prefixEnd_2527560 : Nat := 4983230072969 + 3 ^ 40 * 2527560 * 2
def baseEnd_2527560 : Nat := 432617721026078714525323

theorem tailTrace_2527560 : CollatzResearch.WordTrace tailWord_2527560 prefixEnd_2527560 432617721026078714525323 := by
  unfold tailWord_2527560
  simp only [CollatzResearch.WordTrace]
  refine ⟨46093843361544633862938067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61458457815392845150584089 46093843361544633862938067)
  ·
    refine ⟨69140765042316950794407101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46093843361544633862938067 69140765042316950794407101)
    ·
      refine ⟨25927786890868856547902663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69140765042316950794407101 25927786890868856547902663)
      ·
        refine ⟨38891680336303284821853995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25927786890868856547902663 38891680336303284821853995)
        ·
          refine ⟨58337520504454927232780993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38891680336303284821853995 58337520504454927232780993)
          ·
            refine ⟨43753140378341195424585745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58337520504454927232780993 43753140378341195424585745)
            ·
              refine ⟨32814855283755896568439309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43753140378341195424585745 32814855283755896568439309)
              ·
                refine ⟨12305570731408461213164741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32814855283755896568439309 12305570731408461213164741)
                ·
                  refine ⟨2307294512139086477468389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12305570731408461213164741 2307294512139086477468389)
                  ·
                    refine ⟨432617721026078714525323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2307294512139086477468389 432617721026078714525323)
                    ·
                      rfl

theorem cell23_2527560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 4, 4].length) (baseStart_2527560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2527560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2527560 prefixEnd_2527560 := by exact prefixLift 2527560
  have htrace : WordTrace (prefixWord ++ tailWord_2527560) baseStart_2527560 baseEnd_2527560 := by
    simpa [prefixWord, tailWord_2527560, baseEnd_2527560] using wordTrace_append hprefix tailTrace_2527560
  have hstable : (prefixWord ++ tailWord_2527560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527560).length < 2 ^ (prefixWord ++ tailWord_2527560).sum := by decide
  have hdescent : baseEnd_2527560 < baseStart_2527560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527563 : List Nat := [1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 6]
def baseStart_2527563 : Nat := 118140960795 + 2527563 * 2 ^ 59
def prefixEnd_2527563 : Nat := 4983230072969 + 3 ^ 40 * 2527563 * 2
def baseEnd_2527563 : Nat := 1297854703520199631838455

theorem tailTrace_2527563 : CollatzResearch.WordTrace tailWord_2527563 prefixEnd_2527563 1297854703520199631838455 := by
  unfold tailWord_2527563
  simp only [CollatzResearch.WordTrace]
  refine ⟨92187796142078399238235343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61458530761385599492156895 92187796142078399238235343)
  ·
    refine ⟨138281694213117598857353015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92187796142078399238235343 138281694213117598857353015)
    ·
      refine ⟨207422541319676398286029523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138281694213117598857353015 207422541319676398286029523)
      ·
        refine ⟨311133811979514597429044285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207422541319676398286029523 311133811979514597429044285)
        ·
          refine ⟨116675179492317974035891607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 311133811979514597429044285 116675179492317974035891607)
          ·
            refine ⟨175012769238476961053837411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116675179492317974035891607 175012769238476961053837411)
            ·
              refine ⟨262519153857715441580756117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175012769238476961053837411 262519153857715441580756117)
              ·
                refine ⟨12305585337080411324097943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 262519153857715441580756117 12305585337080411324097943)
                ·
                  refine ⟨18458378005620616986146915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12305585337080411324097943 18458378005620616986146915)
                  ·
                    refine ⟨27687567008430925479220373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18458378005620616986146915 27687567008430925479220373)
                    ·
                      refine ⟨1297854703520199631838455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27687567008430925479220373 1297854703520199631838455)
                      ·
                        rfl

theorem cell23_2527563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 6].length) (baseStart_2527563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2527563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2527563 prefixEnd_2527563 := by exact prefixLift 2527563
  have htrace : WordTrace (prefixWord ++ tailWord_2527563) baseStart_2527563 baseEnd_2527563 := by
    simpa [prefixWord, tailWord_2527563, baseEnd_2527563] using wordTrace_append hprefix tailTrace_2527563
  have hstable : (prefixWord ++ tailWord_2527563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527563).length < 2 ^ (prefixWord ++ tailWord_2527563).sum := by decide
  have hdescent : baseEnd_2527563 < baseStart_2527563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527570 : List Nat := [3, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5]
def baseStart_2527570 : Nat := 118140960795 + 2527570 * 2 ^ 59
def prefixEnd_2527570 : Nat := 4983230072969 + 3 ^ 40 * 2527570 * 2
def baseEnd_2527570 : Nat := 1297858297884781104450923

theorem tailTrace_2527570 : CollatzResearch.WordTrace tailWord_2527570 prefixEnd_2527570 1297858297884781104450923 := by
  unfold tailWord_2527570
  simp only [CollatzResearch.WordTrace]
  refine ⟨23047012863263259858435041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61458700968702026289160109 23047012863263259858435041)
  ·
    refine ⟨17285259647447444893826281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23047012863263259858435041 17285259647447444893826281)
    ·
      refine ⟨12963944735585583670369711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17285259647447444893826281 12963944735585583670369711)
      ·
        refine ⟨19445917103378375505554567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12963944735585583670369711 19445917103378375505554567)
        ·
          refine ⟨29168875655067563258331851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19445917103378375505554567 29168875655067563258331851)
          ·
            refine ⟨43753313482601344887497777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29168875655067563258331851 43753313482601344887497777)
            ·
              refine ⟨32814985111951008665623333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43753313482601344887497777 32814985111951008665623333)
              ·
                refine ⟨6152809708490814124804375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32814985111951008665623333 6152809708490814124804375)
                ·
                  refine ⟨9229214562736221187206563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6152809708490814124804375 9229214562736221187206563)
                  ·
                    refine ⟨13843821844104331780809845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9229214562736221187206563 13843821844104331780809845)
                    ·
                      refine ⟨1297858297884781104450923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13843821844104331780809845 1297858297884781104450923)
                      ·
                        rfl

theorem cell23_2527570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_2527570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2527570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2527570 prefixEnd_2527570 := by exact prefixLift 2527570
  have htrace : WordTrace (prefixWord ++ tailWord_2527570) baseStart_2527570 baseEnd_2527570 := by
    simpa [prefixWord, tailWord_2527570, baseEnd_2527570] using wordTrace_append hprefix tailTrace_2527570
  have hstable : (prefixWord ++ tailWord_2527570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527570).length < 2 ^ (prefixWord ++ tailWord_2527570).sum := by decide
  have hdescent : baseEnd_2527570 < baseStart_2527570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527582 : List Nat := [4, 4, 2, 1, 2, 1, 1, 1, 2, 2, 3]
def baseStart_2527582 : Nat := 118140960795 + 2527582 * 2 ^ 59
def prefixEnd_2527582 : Nat := 4983230072969 + 3 ^ 40 * 2527582 * 2
def baseEnd_2527582 : Nat := 1297864459652635057500869

theorem tailTrace_2527582 : CollatzResearch.WordTrace tailWord_2527582 prefixEnd_2527582 1297864459652635057500869 := by
  unfold tailWord_2527582
  simp only [CollatzResearch.WordTrace]
  refine ⟨11523561141126195685397125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61458992752673043655451333 11523561141126195685397125)
  ·
    refine ⟨2160667713961161691011961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11523561141126195685397125 2160667713961161691011961)
    ·
      refine ⟨1620500785470871268258971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2160667713961161691011961 1620500785470871268258971)
      ·
        refine ⟨2430751178206306902388457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1620500785470871268258971 2430751178206306902388457)
        ·
          refine ⟨1823063383654730176791343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2430751178206306902388457 1823063383654730176791343)
          ·
            refine ⟨2734595075482095265187015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1823063383654730176791343 2734595075482095265187015)
            ·
              refine ⟨4101892613223142897780523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2734595075482095265187015 4101892613223142897780523)
              ·
                refine ⟨6152838919834714346670785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4101892613223142897780523 6152838919834714346670785)
                ·
                  refine ⟨4614629189876035760003089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6152838919834714346670785 4614629189876035760003089)
                  ·
                    refine ⟨3460971892407026820002317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4614629189876035760003089 3460971892407026820002317)
                    ·
                      refine ⟨1297864459652635057500869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3460971892407026820002317 1297864459652635057500869)
                      ·
                        rfl

theorem cell23_2527582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_2527582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2527582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2527582 prefixEnd_2527582 := by exact prefixLift 2527582
  have htrace : WordTrace (prefixWord ++ tailWord_2527582) baseStart_2527582 baseEnd_2527582 := by
    simpa [prefixWord, tailWord_2527582, baseEnd_2527582] using wordTrace_append hprefix tailTrace_2527582
  have hstable : (prefixWord ++ tailWord_2527582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527582).length < 2 ^ (prefixWord ++ tailWord_2527582).sum := by decide
  have hdescent : baseEnd_2527582 < baseStart_2527582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527587 : List Nat := [1, 1, 1, 5, 2, 1, 2, 4, 1, 2, 3]
def baseStart_2527587 : Nat := 118140960795 + 2527587 * 2 ^ 59
def prefixEnd_2527587 : Nat := 4983230072969 + 3 ^ 40 * 2527587 * 2
def baseEnd_2527587 : Nat := 1297867027055907537938345

theorem tailTrace_2527587 : CollatzResearch.WordTrace tailWord_2527587 prefixEnd_2527587 1297867027055907537938345 := by
  unfold tailWord_2527587
  simp only [CollatzResearch.WordTrace]
  refine ⟨92188671493991451337109015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61459114329327634224739343 92188671493991451337109015)
  ·
    refine ⟨138283007240987177005663523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92188671493991451337109015 138283007240987177005663523)
    ·
      refine ⟨207424510861480765508495285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138283007240987177005663523 207424510861480765508495285)
      ·
        refine ⟨19446047893263821766421433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 207424510861480765508495285 19446047893263821766421433)
        ·
          refine ⟨14584535919947866324816075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19446047893263821766421433 14584535919947866324816075)
          ·
            refine ⟨21876803879921799487224113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14584535919947866324816075 21876803879921799487224113)
            ·
              refine ⟨16407602909941349615418085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21876803879921799487224113 16407602909941349615418085)
              ·
                refine ⟨3076425545614003052890891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16407602909941349615418085 3076425545614003052890891)
                ·
                  refine ⟨4614638318421004579336337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3076425545614003052890891 4614638318421004579336337)
                  ·
                    refine ⟨3460978738815753434502253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4614638318421004579336337 3460978738815753434502253)
                    ·
                      refine ⟨1297867027055907537938345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3460978738815753434502253 1297867027055907537938345)
                      ·
                        rfl

theorem cell23_2527587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 4, 1, 2, 3].length) (baseStart_2527587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2527587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2527587 prefixEnd_2527587 := by exact prefixLift 2527587
  have htrace : WordTrace (prefixWord ++ tailWord_2527587) baseStart_2527587 baseEnd_2527587 := by
    simpa [prefixWord, tailWord_2527587, baseEnd_2527587] using wordTrace_append hprefix tailTrace_2527587
  have hstable : (prefixWord ++ tailWord_2527587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527587).length < 2 ^ (prefixWord ++ tailWord_2527587).sum := by decide
  have hdescent : baseEnd_2527587 < baseStart_2527587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527603 : List Nat := [1, 1, 1, 2, 2, 1, 2, 2, 4, 7]
def baseStart_2527603 : Nat := 118140960795 + 2527603 * 2 ^ 59
def prefixEnd_2527603 : Nat := 4983230072969 + 3 ^ 40 * 2527603 * 2
def baseEnd_2527603 : Nat := 432625080915459825112757

theorem tailTrace_2527603 : CollatzResearch.WordTrace tailWord_2527603 prefixEnd_2527603 432625080915459825112757 := by
  unfold tailWord_2527603
  simp only [CollatzResearch.WordTrace]
  refine ⟨92189255061933486069691463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61459503374622324046460975 92189255061933486069691463)
  ·
    refine ⟨138283882592900229104537195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92189255061933486069691463 138283882592900229104537195)
    ·
      refine ⟨207425823889350343656805793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138283882592900229104537195 207425823889350343656805793)
      ·
        refine ⟨155569367917012757742604345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207425823889350343656805793 155569367917012757742604345)
        ·
          refine ⟨116677025937759568306953259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155569367917012757742604345 116677025937759568306953259)
          ·
            refine ⟨175015538906639352460429889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116677025937759568306953259 175015538906639352460429889)
            ·
              refine ⟨131261654179979514345322417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175015538906639352460429889 131261654179979514345322417)
              ·
                refine ⟨98446240634984635758991813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131261654179979514345322417 98446240634984635758991813)
                ·
                  refine ⟨18458670119059619204810965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 98446240634984635758991813 18458670119059619204810965)
                  ·
                    refine ⟨432625080915459825112757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18458670119059619204810965 432625080915459825112757)
                    ·
                      rfl

theorem cell23_2527603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 7].length) (baseStart_2527603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2527603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2527603 prefixEnd_2527603 := by exact prefixLift 2527603
  have htrace : WordTrace (prefixWord ++ tailWord_2527603) baseStart_2527603 baseEnd_2527603 := by
    simpa [prefixWord, tailWord_2527603, baseEnd_2527603] using wordTrace_append hprefix tailTrace_2527603
  have hstable : (prefixWord ++ tailWord_2527603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527603).length < 2 ^ (prefixWord ++ tailWord_2527603).sum := by decide
  have hdescent : baseEnd_2527603 < baseStart_2527603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527657 : List Nat := [1, 2, 1, 1, 1, 1, 3, 6, 1, 4, 2]
def baseStart_2527657 : Nat := 118140960795 + 2527657 * 2 ^ 59
def prefixEnd_2527657 : Nat := 4983230072969 + 3 ^ 40 * 2527657 * 2
def baseEnd_2527657 : Nat := 1297902970701722264063023

theorem tailTrace_2527657 : CollatzResearch.WordTrace tailWord_2527657 prefixEnd_2527657 1297902970701722264063023 := by
  unfold tailWord_2527657
  simp only [CollatzResearch.WordTrace]
  refine ⟨92191224603737853292157225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61460816402491902194771483 92191224603737853292157225)
  ·
    refine ⟨69143418452803389969117919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92191224603737853292157225 69143418452803389969117919)
    ·
      refine ⟨103715127679205084953676879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69143418452803389969117919 103715127679205084953676879)
      ·
        refine ⟨155572691518807627430515319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103715127679205084953676879 155572691518807627430515319)
        ·
          refine ⟨233359037278211441145772979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155572691518807627430515319 233359037278211441145772979)
          ·
            refine ⟨350038555917317161718659469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233359037278211441145772979 350038555917317161718659469)
            ·
              refine ⟨131264458468993935644497301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 350038555917317161718659469 131264458468993935644497301)
              ·
                refine ⟨6153021490734090733335811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 131264458468993935644497301 6153021490734090733335811)
                ·
                  refine ⟨9229532236101136100003717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6153021490734090733335811 9229532236101136100003717)
                  ·
                    refine ⟨1730537294268963018750697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9229532236101136100003717 1730537294268963018750697)
                    ·
                      refine ⟨1297902970701722264063023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1730537294268963018750697 1297902970701722264063023)
                      ·
                        rfl

theorem cell23_2527657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6, 1, 4, 2].length) (baseStart_2527657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2527657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2527657 prefixEnd_2527657 := by exact prefixLift 2527657
  have htrace : WordTrace (prefixWord ++ tailWord_2527657) baseStart_2527657 baseEnd_2527657 := by
    simpa [prefixWord, tailWord_2527657, baseEnd_2527657] using wordTrace_append hprefix tailTrace_2527657
  have hstable : (prefixWord ++ tailWord_2527657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527657).length < 2 ^ (prefixWord ++ tailWord_2527657).sum := by decide
  have hdescent : baseEnd_2527657 < baseStart_2527657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527660 : List Nat := [2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 3]
def baseStart_2527660 : Nat := 118140960795 + 2527660 * 2 ^ 59
def prefixEnd_2527660 : Nat := 4983230072969 + 3 ^ 40 * 2527660 * 2
def baseEnd_2527660 : Nat := 1297904511143685752325509

theorem tailTrace_2527660 : CollatzResearch.WordTrace tailWord_2527660 prefixEnd_2527660 1297904511143685752325509 := by
  unfold tailWord_2527660
  simp only [CollatzResearch.WordTrace]
  refine ⟨46095667011363492402258217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61460889348484656536344289 46095667011363492402258217)
  ·
    refine ⟨34571750258522619301693663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46095667011363492402258217 34571750258522619301693663)
    ·
      refine ⟨51857625387783928952540495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34571750258522619301693663 51857625387783928952540495)
      ·
        refine ⟨77786438081675893428810743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51857625387783928952540495 77786438081675893428810743)
        ·
          refine ⟨116679657122513840143216115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77786438081675893428810743 116679657122513840143216115)
          ·
            refine ⟨175019485683770760214824173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116679657122513840143216115 175019485683770760214824173)
            ·
              refine ⟨65632307131414035080559065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 175019485683770760214824173 65632307131414035080559065)
              ·
                refine ⟨49224230348560526310419299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65632307131414035080559065 49224230348560526310419299)
                ·
                  refine ⟨73836345522840789465628949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49224230348560526310419299 73836345522840789465628949)
                  ·
                    refine ⟨3461078696383162006201357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 73836345522840789465628949 3461078696383162006201357)
                    ·
                      refine ⟨1297904511143685752325509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3461078696383162006201357 1297904511143685752325509)
                      ·
                        rfl

theorem cell23_2527660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 3].length) (baseStart_2527660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2527660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2527660 prefixEnd_2527660 := by exact prefixLift 2527660
  have htrace : WordTrace (prefixWord ++ tailWord_2527660) baseStart_2527660 baseEnd_2527660 := by
    simpa [prefixWord, tailWord_2527660, baseEnd_2527660] using wordTrace_append hprefix tailTrace_2527660
  have hstable : (prefixWord ++ tailWord_2527660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527660).length < 2 ^ (prefixWord ++ tailWord_2527660).sum := by decide
  have hdescent : baseEnd_2527660 < baseStart_2527660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527734 : List Nat := [5, 1, 1, 1, 2, 1, 1, 1, 1, 7, 2]
def baseStart_2527734 : Nat := 118140960795 + 2527734 * 2 ^ 59
def prefixEnd_2527734 : Nat := 4983230072969 + 3 ^ 40 * 2527734 * 2
def baseEnd_2527734 : Nat := 1297942508712118462800169

theorem tailTrace_2527734 : CollatzResearch.WordTrace tailWord_2527734 prefixEnd_2527734 1297942508712118462800169 := by
  unfold tailWord_2527734
  simp only [CollatzResearch.WordTrace]
  refine ⟨5762127064028680965169391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61462688682972596961806837 5762127064028680965169391)
  ·
    refine ⟨8643190596043021447754087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5762127064028680965169391 8643190596043021447754087)
    ·
      refine ⟨12964785894064532171631131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8643190596043021447754087 12964785894064532171631131)
      ·
        refine ⟨19447178841096798257446697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12964785894064532171631131 19447178841096798257446697)
        ·
          refine ⟨14585384130822598693085023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19447178841096798257446697 14585384130822598693085023)
          ·
            refine ⟨21878076196233898039627535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14585384130822598693085023 21878076196233898039627535)
            ·
              refine ⟨32817114294350847059441303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21878076196233898039627535 32817114294350847059441303)
              ·
                refine ⟨49225671441526270589161955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32817114294350847059441303 49225671441526270589161955)
                ·
                  refine ⟨73838507162289405883742933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49225671441526270589161955 73838507162289405883742933)
                  ·
                    refine ⟨1730590011616157950400225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 73838507162289405883742933 1730590011616157950400225)
                    ·
                      refine ⟨1297942508712118462800169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1730590011616157950400225 1297942508712118462800169)
                      ·
                        rfl

theorem cell23_2527734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 1, 7, 2].length) (baseStart_2527734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2527734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2527734 prefixEnd_2527734 := by exact prefixLift 2527734
  have htrace : WordTrace (prefixWord ++ tailWord_2527734) baseStart_2527734 baseEnd_2527734 := by
    simpa [prefixWord, tailWord_2527734, baseEnd_2527734] using wordTrace_append hprefix tailTrace_2527734
  have hstable : (prefixWord ++ tailWord_2527734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527734).length < 2 ^ (prefixWord ++ tailWord_2527734).sum := by decide
  have hdescent : baseEnd_2527734 < baseStart_2527734 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527740 : List Nat := [2, 2, 2, 1, 2, 1, 1, 2, 2, 8]
def baseStart_2527740 : Nat := 118140960795 + 2527740 * 2 ^ 59
def prefixEnd_2527740 : Nat := 4983230072969 + 3 ^ 40 * 2527740 * 2
def baseEnd_2527740 : Nat := 432648529865348479775047

theorem tailTrace_2527740 : CollatzResearch.WordTrace tailWord_2527740 prefixEnd_2527740 432648529865348479775047 := by
  unfold tailWord_2527740
  simp only [CollatzResearch.WordTrace]
  refine ⟨46097125931218579233714337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61462834574958105644952449 46097125931218579233714337)
  ·
    refine ⟨34572844448413934425285753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46097125931218579233714337 34572844448413934425285753)
    ·
      refine ⟨25929633336310450818964315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34572844448413934425285753 25929633336310450818964315)
      ·
        refine ⟨38894450004465676228446473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25929633336310450818964315 38894450004465676228446473)
        ·
          refine ⟨29170837503349257171334855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38894450004465676228446473 29170837503349257171334855)
          ·
            refine ⟨43756256255023885757002283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29170837503349257171334855 43756256255023885757002283)
            ·
              refine ⟨65634384382535828635503425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43756256255023885757002283 65634384382535828635503425)
              ·
                refine ⟨49225788286901871476627569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65634384382535828635503425 49225788286901871476627569)
                ·
                  refine ⟨36919341215176403607470677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49225788286901871476627569 36919341215176403607470677)
                  ·
                    refine ⟨432648529865348479775047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 36919341215176403607470677 432648529865348479775047)
                    ·
                      rfl

theorem cell23_2527740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 2, 8].length) (baseStart_2527740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2527740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2527740 prefixEnd_2527740 := by exact prefixLift 2527740
  have htrace : WordTrace (prefixWord ++ tailWord_2527740) baseStart_2527740 baseEnd_2527740 := by
    simpa [prefixWord, tailWord_2527740, baseEnd_2527740] using wordTrace_append hprefix tailTrace_2527740
  have hstable : (prefixWord ++ tailWord_2527740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527740).length < 2 ^ (prefixWord ++ tailWord_2527740).sum := by decide
  have hdescent : baseEnd_2527740 < baseStart_2527740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527841 : List Nat := [1, 2, 3, 1, 1, 5, 1, 2, 2, 3, 2]
def baseStart_2527841 : Nat := 118140960795 + 2527841 * 2 ^ 59
def prefixEnd_2527841 : Nat := 4983230072969 + 3 ^ 40 * 2527841 * 2
def baseEnd_2527841 : Nat := 1297997451142149544162177

theorem tailTrace_2527841 : CollatzResearch.WordTrace tailWord_2527841 prefixEnd_2527841 1297997451142149544162177 := by
  unfold tailWord_2527841
  simp only [CollatzResearch.WordTrace]
  refine ⟨92197935635071252716855377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61465290423380835144570251 92197935635071252716855377)
  ·
    refine ⟨69148451726303439537641533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92197935635071252716855377 69148451726303439537641533)
    ·
      refine ⟨25930669397363789826615575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69148451726303439537641533 25930669397363789826615575)
      ·
        refine ⟨38896004096045684739923363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25930669397363789826615575 38896004096045684739923363)
        ·
          refine ⟨58344006144068527109885045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38896004096045684739923363 58344006144068527109885045)
          ·
            refine ⟨5469750576006424416551723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58344006144068527109885045 5469750576006424416551723)
            ·
              refine ⟨8204625864009636624827585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5469750576006424416551723 8204625864009636624827585)
              ·
                refine ⟨6153469398007227468620689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8204625864009636624827585 6153469398007227468620689)
                ·
                  refine ⟨4615102048505420601465517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6153469398007227468620689 4615102048505420601465517)
                  ·
                    refine ⟨1730663268189532725549569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4615102048505420601465517 1730663268189532725549569)
                    ·
                      refine ⟨1297997451142149544162177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1730663268189532725549569 1297997451142149544162177)
                      ·
                        rfl

theorem cell23_2527841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 2, 2, 3, 2].length) (baseStart_2527841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2527841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2527841 prefixEnd_2527841 := by exact prefixLift 2527841
  have htrace : WordTrace (prefixWord ++ tailWord_2527841) baseStart_2527841 baseEnd_2527841 := by
    simpa [prefixWord, tailWord_2527841, baseEnd_2527841] using wordTrace_append hprefix tailTrace_2527841
  have hstable : (prefixWord ++ tailWord_2527841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527841).length < 2 ^ (prefixWord ++ tailWord_2527841).sum := by decide
  have hdescent : baseEnd_2527841 < baseStart_2527841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527842 : List Nat := [3, 3, 2, 3, 1, 1, 3, 2, 1, 4]
def baseStart_2527842 : Nat := 118140960795 + 2527842 * 2 ^ 59
def prefixEnd_2527842 : Nat := 4983230072969 + 3 ^ 40 * 2527842 * 2
def baseEnd_2527842 : Nat := 432665988207601346749891

theorem tailTrace_2527842 : CollatzResearch.WordTrace tailWord_2527842 prefixEnd_2527842 432665988207601346749891 := by
  unfold tailWord_2527842
  simp only [CollatzResearch.WordTrace]
  refine ⟨23049493027016907471910445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61465314738711753258427853 23049493027016907471910445)
  ·
    refine ⟨8643559885131340301966417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23049493027016907471910445 8643559885131340301966417)
    ·
      refine ⟨6482669913848505226474813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8643559885131340301966417 6482669913848505226474813)
      ·
        refine ⟨2431001217693189459928055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6482669913848505226474813 2431001217693189459928055)
        ·
          refine ⟨3646501826539784189892083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2431001217693189459928055 3646501826539784189892083)
          ·
            refine ⟨5469752739809676284838125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3646501826539784189892083 5469752739809676284838125)
            ·
              refine ⟨2051157277428628606814297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5469752739809676284838125 2051157277428628606814297)
              ·
                refine ⟨1538367958071471455110723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2051157277428628606814297 1538367958071471455110723)
                ·
                  refine ⟨2307551937107207182666085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1538367958071471455110723 2307551937107207182666085)
                  ·
                    refine ⟨432665988207601346749891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2307551937107207182666085 432665988207601346749891)
                    ·
                      rfl

theorem cell23_2527842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_2527842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2527842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2527842 prefixEnd_2527842 := by exact prefixLift 2527842
  have htrace : WordTrace (prefixWord ++ tailWord_2527842) baseStart_2527842 baseEnd_2527842 := by
    simpa [prefixWord, tailWord_2527842, baseEnd_2527842] using wordTrace_append hprefix tailTrace_2527842
  have hstable : (prefixWord ++ tailWord_2527842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527842).length < 2 ^ (prefixWord ++ tailWord_2527842).sum := by decide
  have hdescent : baseEnd_2527842 < baseStart_2527842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527857 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 1, 8, 3]
def baseStart_2527857 : Nat := 118140960795 + 2527857 * 2 ^ 59
def prefixEnd_2527857 : Nat := 4983230072969 + 3 ^ 40 * 2527857 * 2
def baseEnd_2527857 : Nat := 1298005666832621481562103

theorem tailTrace_2527857 : CollatzResearch.WordTrace tailWord_2527857 prefixEnd_2527857 1298005666832621481562103 := by
  unfold tailWord_2527857
  simp only [CollatzResearch.WordTrace]
  refine ⟨92198519203013287449437825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61465679468675524966291883 92198519203013287449437825)
  ·
    refine ⟨69148889402259965587078369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92198519203013287449437825 69148889402259965587078369)
    ·
      refine ⟨51861667051694974190308777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69148889402259965587078369 51861667051694974190308777)
      ·
        refine ⟨38896250288771230642731583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51861667051694974190308777 38896250288771230642731583)
        ·
          refine ⟨58344375433156845964097375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38896250288771230642731583 58344375433156845964097375)
          ·
            refine ⟨87516563149735268946146063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58344375433156845964097375 87516563149735268946146063)
            ·
              refine ⟨131274844724602903419219095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87516563149735268946146063 131274844724602903419219095)
              ·
                refine ⟨196912267086904355128828643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131274844724602903419219095 196912267086904355128828643)
                ·
                  refine ⟨295368400630356532693242965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 196912267086904355128828643 295368400630356532693242965)
                  ·
                    refine ⟨3461348444886990617498941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 295368400630356532693242965 3461348444886990617498941)
                    ·
                      refine ⟨1298005666832621481562103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3461348444886990617498941 1298005666832621481562103)
                      ·
                        rfl

theorem cell23_2527857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 8, 3].length) (baseStart_2527857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2527857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2527857 prefixEnd_2527857 := by exact prefixLift 2527857
  have htrace : WordTrace (prefixWord ++ tailWord_2527857) baseStart_2527857 baseEnd_2527857 := by
    simpa [prefixWord, tailWord_2527857, baseEnd_2527857] using wordTrace_append hprefix tailTrace_2527857
  have hstable : (prefixWord ++ tailWord_2527857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527857).length < 2 ^ (prefixWord ++ tailWord_2527857).sum := by decide
  have hdescent : baseEnd_2527857 < baseStart_2527857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527864 : List Nat := [2, 1, 2, 1, 1, 1, 2, 7, 2, 4]
def baseStart_2527864 : Nat := 118140960795 + 2527864 * 2 ^ 59
def prefixEnd_2527864 : Nat := 4983230072969 + 3 ^ 40 * 2527864 * 2
def baseEnd_2527864 : Nat := 432669753732400984724857

theorem tailTrace_2527864 : CollatzResearch.WordTrace tailWord_2527864 prefixEnd_2527864 432669753732400984724857 := by
  unfold tailWord_2527864
  simp only [CollatzResearch.WordTrace]
  refine ⟨46099387256993963822471323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61465849675991951763295097 46099387256993963822471323)
  ·
    refine ⟨69149080885490945733706985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46099387256993963822471323 69149080885490945733706985)
    ·
      refine ⟨51861810664118209300280239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69149080885490945733706985 51861810664118209300280239)
      ·
        refine ⟨77792715996177313950420359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51861810664118209300280239 77792715996177313950420359)
        ·
          refine ⟨116689073994265970925630539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77792715996177313950420359 116689073994265970925630539)
          ·
            refine ⟨175033610991398956388445809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116689073994265970925630539 175033610991398956388445809)
            ·
              refine ⟨131275208243549217291334357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175033610991398956388445809 131275208243549217291334357)
              ·
                refine ⟨3076762693208184780265649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 131275208243549217291334357 3076762693208184780265649)
                ·
                  refine ⟨2307572019906138585199237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3076762693208184780265649 2307572019906138585199237)
                  ·
                    refine ⟨432669753732400984724857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2307572019906138585199237 432669753732400984724857)
                    ·
                      rfl

theorem cell23_2527864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 7, 2, 4].length) (baseStart_2527864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2527864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2527864 prefixEnd_2527864 := by exact prefixLift 2527864
  have htrace : WordTrace (prefixWord ++ tailWord_2527864) baseStart_2527864 baseEnd_2527864 := by
    simpa [prefixWord, tailWord_2527864, baseEnd_2527864] using wordTrace_append hprefix tailTrace_2527864
  have hstable : (prefixWord ++ tailWord_2527864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527864).length < 2 ^ (prefixWord ++ tailWord_2527864).sum := by decide
  have hdescent : baseEnd_2527864 < baseStart_2527864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527877 : List Nat := [1, 3, 1, 1, 4, 2, 2, 9]
def baseStart_2527877 : Nat := 118140960795 + 2527877 * 2 ^ 59
def prefixEnd_2527877 : Nat := 4983230072969 + 3 ^ 40 * 2527877 * 2
def baseEnd_2527877 : Nat := 48074664312804126048593

theorem tailTrace_2527877 : CollatzResearch.WordTrace tailWord_2527877 prefixEnd_2527877 48074664312804126048593 := by
  unfold tailWord_2527877
  simp only [CollatzResearch.WordTrace]
  refine ⟨92199248662940830865165885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61466165775293887243443923 92199248662940830865165885)
  ·
    refine ⟨34574718248602811574437207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92199248662940830865165885 34574718248602811574437207)
    ·
      refine ⟨51862077372904217361655811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34574718248602811574437207 51862077372904217361655811)
      ·
        refine ⟨77793116059356326042483717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51862077372904217361655811 77793116059356326042483717)
        ·
          refine ⟨14586209261129311132965697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77793116059356326042483717 14586209261129311132965697)
          ·
            refine ⟨10939656945846983349724273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14586209261129311132965697 10939656945846983349724273)
            ·
              refine ⟨8204742709385237512293205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10939656945846983349724273 8204742709385237512293205)
              ·
                refine ⟨48074664312804126048593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8204742709385237512293205 48074664312804126048593)
                ·
                  rfl

theorem cell23_2527877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 9].length) (baseStart_2527877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2527877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2527877 prefixEnd_2527877 := by exact prefixLift 2527877
  have htrace : WordTrace (prefixWord ++ tailWord_2527877) baseStart_2527877 baseEnd_2527877 := by
    simpa [prefixWord, tailWord_2527877, baseEnd_2527877] using wordTrace_append hprefix tailTrace_2527877
  have hstable : (prefixWord ++ tailWord_2527877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527877).length < 2 ^ (prefixWord ++ tailWord_2527877).sum := by decide
  have hdescent : baseEnd_2527877 < baseStart_2527877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527918 : List Nat := [4, 1, 4, 1, 1, 2, 2, 1, 1, 2, 4]
def baseStart_2527918 : Nat := 118140960795 + 2527918 * 2 ^ 59
def prefixEnd_2527918 : Nat := 4983230072969 + 3 ^ 40 * 2527918 * 2
def baseEnd_2527918 : Nat := 1298036989152545742899323

theorem tailTrace_2527918 : CollatzResearch.WordTrace tailWord_2527918 prefixEnd_2527918 1298036989152545742899323 := by
  unfold tailWord_2527918
  simp only [CollatzResearch.WordTrace]
  refine ⟨11525093006974036858426051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61467162703861529911605605 11525093006974036858426051)
  ·
    refine ⟨17287639510461055287639077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11525093006974036858426051 17287639510461055287639077)
    ·
      refine ⟨3241432408211447866432327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17287639510461055287639077 3241432408211447866432327)
      ·
        refine ⟨4862148612317171799648491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3241432408211447866432327 4862148612317171799648491)
        ·
          refine ⟨7293222918475757699472737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4862148612317171799648491 7293222918475757699472737)
          ·
            refine ⟨5469917188856818274604553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7293222918475757699472737 5469917188856818274604553)
            ·
              refine ⟨4102437891642613705953415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5469917188856818274604553 4102437891642613705953415)
              ·
                refine ⟨6153656837463920558930123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4102437891642613705953415 6153656837463920558930123)
                ·
                  refine ⟨9230485256195880838395185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6153656837463920558930123 9230485256195880838395185)
                  ·
                    refine ⟨6922863942146910628796389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9230485256195880838395185 6922863942146910628796389)
                    ·
                      refine ⟨1298036989152545742899323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6922863942146910628796389 1298036989152545742899323)
                      ·
                        rfl

theorem cell23_2527918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_2527918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2527918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2527918 prefixEnd_2527918 := by exact prefixLift 2527918
  have htrace : WordTrace (prefixWord ++ tailWord_2527918) baseStart_2527918 baseEnd_2527918 := by
    simpa [prefixWord, tailWord_2527918, baseEnd_2527918] using wordTrace_append hprefix tailTrace_2527918
  have hstable : (prefixWord ++ tailWord_2527918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527918).length < 2 ^ (prefixWord ++ tailWord_2527918).sum := by decide
  have hdescent : baseEnd_2527918 < baseStart_2527918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527934 : List Nat := [4, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5]
def baseStart_2527934 : Nat := 118140960795 + 2527934 * 2 ^ 59
def prefixEnd_2527934 : Nat := 4983230072969 + 3 ^ 40 * 2527934 * 2
def baseEnd_2527934 : Nat := 1298045204843017680299249

theorem tailTrace_2527934 : CollatzResearch.WordTrace tailWord_2527934 prefixEnd_2527934 1298045204843017680299249 := by
  unfold tailWord_2527934
  simp only [CollatzResearch.WordTrace]
  refine ⟨11525165952966791199998857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61467551749156219733327237 11525165952966791199998857)
  ·
    refine ⟨8643874464725093399999143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11525165952966791199998857 8643874464725093399999143)
    ·
      refine ⟨12965811697087640099998715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8643874464725093399999143 12965811697087640099998715)
      ·
        refine ⟨19448717545631460149998073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12965811697087640099998715 19448717545631460149998073)
        ·
          refine ⟨14586538159223595112498555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19448717545631460149998073 14586538159223595112498555)
          ·
            refine ⟨21879807238835392668747833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14586538159223595112498555 21879807238835392668747833)
            ·
              refine ⟨16409855429126544501560875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21879807238835392668747833 16409855429126544501560875)
              ·
                refine ⟨24614783143689816752341313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16409855429126544501560875 24614783143689816752341313)
                ·
                  refine ⟨18461087357767362564255985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24614783143689816752341313 18461087357767362564255985)
                  ·
                    refine ⟨13845815518325521923191989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18461087357767362564255985 13845815518325521923191989)
                    ·
                      refine ⟨1298045204843017680299249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13845815518325521923191989 1298045204843017680299249)
                      ·
                        rfl

theorem cell23_2527934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_2527934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2527934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2527934 prefixEnd_2527934 := by exact prefixLift 2527934
  have htrace : WordTrace (prefixWord ++ tailWord_2527934) baseStart_2527934 baseEnd_2527934 := by
    simpa [prefixWord, tailWord_2527934, baseEnd_2527934] using wordTrace_append hprefix tailTrace_2527934
  have hstable : (prefixWord ++ tailWord_2527934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527934).length < 2 ^ (prefixWord ++ tailWord_2527934).sum := by decide
  have hdescent : baseEnd_2527934 < baseStart_2527934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527942 : List Nat := [6, 1, 2, 1, 2, 1, 1, 3, 1, 2, 3]
def baseStart_2527942 : Nat := 118140960795 + 2527942 * 2 ^ 59
def prefixEnd_2527942 : Nat := 4983230072969 + 3 ^ 40 * 2527942 * 2
def baseEnd_2527942 : Nat := 1298049312688253648999213

theorem tailTrace_2527942 : CollatzResearch.WordTrace tailWord_2527942 prefixEnd_2527942 1298049312688253648999213 := by
  unfold tailWord_2527942
  simp only [CollatzResearch.WordTrace]
  refine ⟨2881300606490792092696315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 61467746271803564644188053 2881300606490792092696315)
  ·
    refine ⟨4321950909736188139044473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2881300606490792092696315 4321950909736188139044473)
    ·
      refine ⟨3241463182302141104283355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4321950909736188139044473 3241463182302141104283355)
      ·
        refine ⟨4862194773453211656425033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3241463182302141104283355 4862194773453211656425033)
        ·
          refine ⟨3646646080089908742318775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4862194773453211656425033 3646646080089908742318775)
          ·
            refine ⟨5469969120134863113478163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3646646080089908742318775 5469969120134863113478163)
            ·
              refine ⟨8204953680202294670217245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5469969120134863113478163 8204953680202294670217245)
              ·
                refine ⟨3076857630075860501331467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8204953680202294670217245 3076857630075860501331467)
                ·
                  refine ⟨4615286445113790751997201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3076857630075860501331467 4615286445113790751997201)
                  ·
                    refine ⟨3461464833835343063997901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4615286445113790751997201 3461464833835343063997901)
                    ·
                      refine ⟨1298049312688253648999213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3461464833835343063997901 1298049312688253648999213)
                      ·
                        rfl

theorem cell23_2527942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_2527942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2527942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2527942 prefixEnd_2527942 := by exact prefixLift 2527942
  have htrace : WordTrace (prefixWord ++ tailWord_2527942) baseStart_2527942 baseEnd_2527942 := by
    simpa [prefixWord, tailWord_2527942, baseEnd_2527942] using wordTrace_append hprefix tailTrace_2527942
  have hstable : (prefixWord ++ tailWord_2527942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527942).length < 2 ^ (prefixWord ++ tailWord_2527942).sum := by decide
  have hdescent : baseEnd_2527942 < baseStart_2527942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527994 : List Nat := [3, 1, 1, 1, 1, 3, 2, 2, 1, 5, 3]
def baseStart_2527994 : Nat := 118140960795 + 2527994 * 2 ^ 59
def prefixEnd_2527994 : Nat := 4983230072969 + 3 ^ 40 * 2527994 * 2
def baseEnd_2527994 : Nat := 1298076013682287445548973

theorem tailTrace_2527994 : CollatzResearch.WordTrace tailWord_2527994 prefixEnd_2527994 1298076013682287445548973 := by
  unfold tailWord_2527994
  simp only [CollatzResearch.WordTrace]
  refine ⟨23050879000879239961793759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61469010669011306564783357 23050879000879239961793759)
  ·
    refine ⟨34576318501318859942690639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23050879000879239961793759 34576318501318859942690639)
    ·
      refine ⟨51864477751978289914035959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34576318501318859942690639 51864477751978289914035959)
      ·
        refine ⟨77796716627967434871053939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51864477751978289914035959 77796716627967434871053939)
        ·
          refine ⟨116695074941951152306580909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77796716627967434871053939 116695074941951152306580909)
          ·
            refine ⟨43760653103231682114967841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116695074941951152306580909 43760653103231682114967841)
            ·
              refine ⟨32820489827423761586225881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43760653103231682114967841 32820489827423761586225881)
              ·
                refine ⟨24615367370567821189669411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32820489827423761586225881 24615367370567821189669411)
                ·
                  refine ⟨36923051055851731784504117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24615367370567821189669411 36923051055851731784504117)
                  ·
                    refine ⟨3461536036486099854797261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36923051055851731784504117 3461536036486099854797261)
                    ·
                      refine ⟨1298076013682287445548973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3461536036486099854797261 1298076013682287445548973)
                      ·
                        rfl

theorem cell23_2527994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 1, 5, 3].length) (baseStart_2527994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2527994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2527994 prefixEnd_2527994 := by exact prefixLift 2527994
  have htrace : WordTrace (prefixWord ++ tailWord_2527994) baseStart_2527994 baseEnd_2527994 := by
    simpa [prefixWord, tailWord_2527994, baseEnd_2527994] using wordTrace_append hprefix tailTrace_2527994
  have hstable : (prefixWord ++ tailWord_2527994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527994).length < 2 ^ (prefixWord ++ tailWord_2527994).sum := by decide
  have hdescent : baseEnd_2527994 < baseStart_2527994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528021 : List Nat := [1, 3, 2, 1, 2, 2, 2, 1, 2, 5, 2]
def baseStart_2528021 : Nat := 118140960795 + 2528021 * 2 ^ 59
def prefixEnd_2528021 : Nat := 4983230072969 + 3 ^ 40 * 2528021 * 2
def baseEnd_2528021 : Nat := 1298089877659958839911349

theorem tailTrace_2528021 : CollatzResearch.WordTrace tailWord_2528021 prefixEnd_2528021 1298089877659958839911349 := by
  unfold tailWord_2528021
  simp only [CollatzResearch.WordTrace]
  refine ⟨92204500774419143458407917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61469667182946095638938611 92204500774419143458407917)
  ·
    refine ⟨34576687790407178796902969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92204500774419143458407917 34576687790407178796902969)
    ·
      refine ⟨25932515842805384097677227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34576687790407178796902969 25932515842805384097677227)
      ·
        refine ⟨38898773764208076146515841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25932515842805384097677227 38898773764208076146515841)
        ·
          refine ⟨29174080323156057109886881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38898773764208076146515841 29174080323156057109886881)
          ·
            refine ⟨21880560242367042832415161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29174080323156057109886881 21880560242367042832415161)
            ·
              refine ⟨16410420181775282124311371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21880560242367042832415161 16410420181775282124311371)
              ·
                refine ⟨24615630272662923186467057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16410420181775282124311371 24615630272662923186467057)
                ·
                  refine ⟨18461722704497192389850293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24615630272662923186467057 18461722704497192389850293)
                  ·
                    refine ⟨1730786503546611786548465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18461722704497192389850293 1730786503546611786548465)
                    ·
                      refine ⟨1298089877659958839911349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1730786503546611786548465 1298089877659958839911349)
                      ·
                        rfl

theorem cell23_2528021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 5, 2].length) (baseStart_2528021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2528021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2528021 prefixEnd_2528021 := by exact prefixLift 2528021
  have htrace : WordTrace (prefixWord ++ tailWord_2528021) baseStart_2528021 baseEnd_2528021 := by
    simpa [prefixWord, tailWord_2528021, baseEnd_2528021] using wordTrace_append hprefix tailTrace_2528021
  have hstable : (prefixWord ++ tailWord_2528021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528021).length < 2 ^ (prefixWord ++ tailWord_2528021).sum := by decide
  have hdescent : baseEnd_2528021 < baseStart_2528021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528051 : List Nat := [1, 1, 1, 2, 6, 1, 1, 3, 2, 1, 4]
def baseStart_2528051 : Nat := 118140960795 + 2528051 * 2 ^ 59
def prefixEnd_2528051 : Nat := 4983230072969 + 3 ^ 40 * 2528051 * 2
def baseEnd_2528051 : Nat := 1298105282079593722536211

theorem tailTrace_2528051 : CollatzResearch.WordTrace tailWord_2528051 prefixEnd_2528051 1298105282079593722536211 := by
  unfold tailWord_2528051
  simp only [CollatzResearch.WordTrace]
  refine ⟨92205594964310458582000007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61470396642873639054666671 92205594964310458582000007)
  ·
    refine ⟨138308392446465687873000011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92205594964310458582000007 138308392446465687873000011)
    ·
      refine ⟨207462588669698531809500017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138308392446465687873000011 207462588669698531809500017)
      ·
        refine ⟨155596941502273898857125013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207462588669698531809500017 155596941502273898857125013)
        ·
          refine ⟨7293606632919089008927735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 155596941502273898857125013 7293606632919089008927735)
          ·
            refine ⟨10940409949378633513391603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7293606632919089008927735 10940409949378633513391603)
            ·
              refine ⟨16410614924067950270087405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10940409949378633513391603 16410614924067950270087405)
              ·
                refine ⟨6153980596525481351282777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16410614924067950270087405 6153980596525481351282777)
                ·
                  refine ⟨4615485447394111013462083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6153980596525481351282777 4615485447394111013462083)
                  ·
                    refine ⟨6923228171091166520193125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4615485447394111013462083 6923228171091166520193125)
                    ·
                      refine ⟨1298105282079593722536211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6923228171091166520193125 1298105282079593722536211)
                      ·
                        rfl

theorem cell23_2528051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 3, 2, 1, 4].length) (baseStart_2528051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2528051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2528051 prefixEnd_2528051 := by exact prefixLift 2528051
  have htrace : WordTrace (prefixWord ++ tailWord_2528051) baseStart_2528051 baseEnd_2528051 := by
    simpa [prefixWord, tailWord_2528051, baseEnd_2528051] using wordTrace_append hprefix tailTrace_2528051
  have hstable : (prefixWord ++ tailWord_2528051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528051).length < 2 ^ (prefixWord ++ tailWord_2528051).sum := by decide
  have hdescent : baseEnd_2528051 < baseStart_2528051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528135 : List Nat := [1, 1, 4, 2, 3, 2, 2, 1, 3, 1, 3]
def baseStart_2528135 : Nat := 118140960795 + 2528135 * 2 ^ 59
def prefixEnd_2528135 : Nat := 4983230072969 + 3 ^ 40 * 2528135 * 2
def baseEnd_2528135 : Nat := 1298148414454571393885825

theorem tailTrace_2528135 : CollatzResearch.WordTrace tailWord_2528135 prefixEnd_2528135 1298148414454571393885825 := by
  unfold tailWord_2528135
  simp only [CollatzResearch.WordTrace]
  refine ⟨92208658696006140928057859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61472439130670760618705239 92208658696006140928057859)
  ·
    refine ⟨138312988044009211392086789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92208658696006140928057859 138312988044009211392086789)
    ·
      refine ⟨25933685258251727136016273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 138312988044009211392086789 25933685258251727136016273)
      ·
        refine ⟨19450263943688795352012205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25933685258251727136016273 19450263943688795352012205)
        ·
          refine ⟨7293848978883298257004577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19450263943688795352012205 7293848978883298257004577)
          ·
            refine ⟨5470386734162473692753433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7293848978883298257004577 5470386734162473692753433)
            ·
              refine ⟨4102790050621855269565075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5470386734162473692753433 4102790050621855269565075)
              ·
                refine ⟨6154185075932782904347613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4102790050621855269565075 6154185075932782904347613)
                ·
                  refine ⟨2307819403474793589130355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6154185075932782904347613 2307819403474793589130355)
                  ·
                    refine ⟨3461729105212190383695533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2307819403474793589130355 3461729105212190383695533)
                    ·
                      refine ⟨1298148414454571393885825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3461729105212190383695533 1298148414454571393885825)
                      ·
                        rfl

theorem cell23_2528135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 1, 3, 1, 3].length) (baseStart_2528135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2528135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2528135 prefixEnd_2528135 := by exact prefixLift 2528135
  have htrace : WordTrace (prefixWord ++ tailWord_2528135) baseStart_2528135 baseEnd_2528135 := by
    simpa [prefixWord, tailWord_2528135, baseEnd_2528135] using wordTrace_append hprefix tailTrace_2528135
  have hstable : (prefixWord ++ tailWord_2528135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528135).length < 2 ^ (prefixWord ++ tailWord_2528135).sum := by decide
  have hdescent : baseEnd_2528135 < baseStart_2528135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528144 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 5]
def baseStart_2528144 : Nat := 118140960795 + 2528144 * 2 ^ 59
def prefixEnd_2528144 : Nat := 4983230072969 + 3 ^ 40 * 2528144 * 2
def baseEnd_2528144 : Nat := 1298153035780461858673283

theorem tailTrace_2528144 : CollatzResearch.WordTrace tailWord_2528144 prefixEnd_2528144 1298153035780461858673283 := by
  unfold tailWord_2528144
  simp only [CollatzResearch.WordTrace]
  refine ⟨46104493476486767732567743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61472657968649023643423657 46104493476486767732567743)
  ·
    refine ⟨69156740214730151598851615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46104493476486767732567743 69156740214730151598851615)
    ·
      refine ⟨103735110322095227398277423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69156740214730151598851615 103735110322095227398277423)
      ·
        refine ⟨155602665483142841097416135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103735110322095227398277423 155602665483142841097416135)
        ·
          refine ⟨233403998224714261646124203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155602665483142841097416135 233403998224714261646124203)
          ·
            refine ⟨350105997337071392469186305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233403998224714261646124203 350105997337071392469186305)
            ·
              refine ⟨262579498002803544351889729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 350105997337071392469186305 262579498002803544351889729)
              ·
                refine ⟨196934623502102658263917297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 262579498002803544351889729 196934623502102658263917297)
                ·
                  refine ⟨147700967626576993697937973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 196934623502102658263917297 147700967626576993697937973)
                  ·
                    refine ⟨13846965714991593159181685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 147700967626576993697937973 13846965714991593159181685)
                    ·
                      refine ⟨1298153035780461858673283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13846965714991593159181685 1298153035780461858673283)
                      ·
                        rfl

theorem cell23_2528144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 5].length) (baseStart_2528144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2528144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2528144 prefixEnd_2528144 := by exact prefixLift 2528144
  have htrace : WordTrace (prefixWord ++ tailWord_2528144) baseStart_2528144 baseEnd_2528144 := by
    simpa [prefixWord, tailWord_2528144, baseEnd_2528144] using wordTrace_append hprefix tailTrace_2528144
  have hstable : (prefixWord ++ tailWord_2528144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528144).length < 2 ^ (prefixWord ++ tailWord_2528144).sum := by decide
  have hdescent : baseEnd_2528144 < baseStart_2528144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528191 : List Nat := [1, 1, 2, 2, 2, 1, 2, 1, 5, 3, 3]
def baseStart_2528191 : Nat := 118140960795 + 2528191 * 2 ^ 59
def prefixEnd_2528191 : Nat := 4983230072969 + 3 ^ 40 * 2528191 * 2
def baseEnd_2528191 : Nat := 1298177169371223174785567

theorem tailTrace_2528191 : CollatzResearch.WordTrace tailWord_2528191 prefixEnd_2528191 1298177169371223174785567 := by
  unfold tailWord_2528191
  simp only [CollatzResearch.WordTrace]
  refine ⟨92210701183803262492096427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61473800789202174994730951 92210701183803262492096427)
  ·
    refine ⟨138316051775704893738144641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92210701183803262492096427 138316051775704893738144641)
    ·
      refine ⟨103737038831778670303608481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138316051775704893738144641 103737038831778670303608481)
      ·
        refine ⟨77802779123834002727706361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103737038831778670303608481 77802779123834002727706361)
        ·
          refine ⟨58352084342875502045779771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77802779123834002727706361 58352084342875502045779771)
          ·
            refine ⟨87528126514313253068669657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58352084342875502045779771 87528126514313253068669657)
            ·
              refine ⟨65646094885734939801502243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87528126514313253068669657 65646094885734939801502243)
              ·
                refine ⟨98469142328602409702253365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65646094885734939801502243 98469142328602409702253365)
                ·
                  refine ⟨9231482093306475909586253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 98469142328602409702253365 9231482093306475909586253)
                  ·
                    refine ⟨3461805784989928466094845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9231482093306475909586253 3461805784989928466094845)
                    ·
                      refine ⟨1298177169371223174785567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3461805784989928466094845 1298177169371223174785567)
                      ·
                        rfl

theorem cell23_2528191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5, 3, 3].length) (baseStart_2528191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2528191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2528191 prefixEnd_2528191 := by exact prefixLift 2528191
  have htrace : WordTrace (prefixWord ++ tailWord_2528191) baseStart_2528191 baseEnd_2528191 := by
    simpa [prefixWord, tailWord_2528191, baseEnd_2528191] using wordTrace_append hprefix tailTrace_2528191
  have hstable : (prefixWord ++ tailWord_2528191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528191).length < 2 ^ (prefixWord ++ tailWord_2528191).sum := by decide
  have hdescent : baseEnd_2528191 < baseStart_2528191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528192 : List Nat := [2, 1, 1, 2, 3, 5, 1, 1, 3, 2, 2]
def baseStart_2528192 : Nat := 118140960795 + 2528192 * 2 ^ 59
def prefixEnd_2528192 : Nat := 4983230072969 + 3 ^ 40 * 2528192 * 2
def baseEnd_2528192 : Nat := 1298177682851877670873063

theorem tailTrace_2528192 : CollatzResearch.WordTrace tailWord_2528192 prefixEnd_2528192 1298177682851877670873063 := by
  unfold tailWord_2528192
  simp only [CollatzResearch.WordTrace]
  refine ⟨46105368828399819831441415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61473825104533093108588553 46105368828399819831441415)
  ·
    refine ⟨69158053242599729747162123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46105368828399819831441415 69158053242599729747162123)
    ·
      refine ⟨103737079863899594620743185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69158053242599729747162123 103737079863899594620743185)
      ·
        refine ⟨77802809897924695965557389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103737079863899594620743185 77802809897924695965557389)
        ·
          refine ⟨29176053711721760987084021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77802809897924695965557389 29176053711721760987084021)
          ·
            refine ⟨2735255035473915092539127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29176053711721760987084021 2735255035473915092539127)
            ·
              refine ⟨4102882553210872638808691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2735255035473915092539127 4102882553210872638808691)
              ·
                refine ⟨6154323829816308958213037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4102882553210872638808691 6154323829816308958213037)
                ·
                  refine ⟨2307871436181115859329889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6154323829816308958213037 2307871436181115859329889)
                  ·
                    refine ⟨1730903577135836894497417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2307871436181115859329889 1730903577135836894497417)
                    ·
                      refine ⟨1298177682851877670873063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1730903577135836894497417 1298177682851877670873063)
                      ·
                        rfl

theorem cell23_2528192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 1, 3, 2, 2].length) (baseStart_2528192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2528192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2528192 prefixEnd_2528192 := by exact prefixLift 2528192
  have htrace : WordTrace (prefixWord ++ tailWord_2528192) baseStart_2528192 baseEnd_2528192 := by
    simpa [prefixWord, tailWord_2528192, baseEnd_2528192] using wordTrace_append hprefix tailTrace_2528192
  have hstable : (prefixWord ++ tailWord_2528192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528192).length < 2 ^ (prefixWord ++ tailWord_2528192).sum := by decide
  have hdescent : baseEnd_2528192 < baseStart_2528192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528212 : List Nat := [2, 4, 1, 2, 1, 4, 1, 2, 1, 2, 3]
def baseStart_2528212 : Nat := 118140960795 + 2528212 * 2 ^ 59
def prefixEnd_2528212 : Nat := 4983230072969 + 3 ^ 40 * 2528212 * 2
def baseEnd_2528212 : Nat := 1298187952464967592622971

theorem tailTrace_2528212 : CollatzResearch.WordTrace tailWord_2528212 prefixEnd_2528212 1298187952464967592622971 := by
  unfold tailWord_2528212
  simp only [CollatzResearch.WordTrace]
  refine ⟨46105733558363591539305445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61474311411151455385740593 46105733558363591539305445)
  ·
    refine ⟨8644825042193173413619771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46105733558363591539305445 8644825042193173413619771)
    ·
      refine ⟨12967237563289760120429657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8644825042193173413619771 12967237563289760120429657)
      ·
        refine ⟨9725428172467320090322243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12967237563289760120429657 9725428172467320090322243)
        ·
          refine ⟨14588142258700980135483365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9725428172467320090322243 14588142258700980135483365)
          ·
            refine ⟨2735276673506433775403131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14588142258700980135483365 2735276673506433775403131)
            ·
              refine ⟨4102915010259650663104697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2735276673506433775403131 4102915010259650663104697)
              ·
                refine ⟨3077186257694737997328523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4102915010259650663104697 3077186257694737997328523)
                ·
                  refine ⟨4615779386542106995992785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3077186257694737997328523 4615779386542106995992785)
                  ·
                    refine ⟨3461834539906580246994589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4615779386542106995992785 3461834539906580246994589)
                    ·
                      refine ⟨1298187952464967592622971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3461834539906580246994589 1298187952464967592622971)
                      ·
                        rfl

theorem cell23_2528212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_2528212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2528212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2528212 prefixEnd_2528212 := by exact prefixLift 2528212
  have htrace : WordTrace (prefixWord ++ tailWord_2528212) baseStart_2528212 baseEnd_2528212 := by
    simpa [prefixWord, tailWord_2528212, baseEnd_2528212] using wordTrace_append hprefix tailTrace_2528212
  have hstable : (prefixWord ++ tailWord_2528212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528212).length < 2 ^ (prefixWord ++ tailWord_2528212).sum := by decide
  have hdescent : baseEnd_2528212 < baseStart_2528212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528229 : List Nat := [1, 3, 1, 6, 1, 1, 3, 1, 1, 2, 3]
def baseStart_2528229 : Nat := 118140960795 + 2528229 * 2 ^ 59
def prefixEnd_2528229 : Nat := 4983230072969 + 3 ^ 40 * 2528229 * 2
def baseEnd_2528229 : Nat := 1298196681636094026110393

theorem tailTrace_2528229 : CollatzResearch.WordTrace tailWord_2528229 prefixEnd_2528229 1298196681636094026110393 := by
  unfold tailWord_2528229
  simp only [CollatzResearch.WordTrace]
  refine ⟨92212087157665594981979741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61474724771777063321319827 92212087157665594981979741)
  ·
    refine ⟨34579532684124598118242403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92212087157665594981979741 34579532684124598118242403)
    ·
      refine ⟨51869299026186897177363605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34579532684124598118242403 51869299026186897177363605)
      ·
        refine ⟨2431373391852510805188919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 51869299026186897177363605 2431373391852510805188919)
        ·
          refine ⟨3647060087778766207783379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2431373391852510805188919 3647060087778766207783379)
          ·
            refine ⟨5470590131668149311675069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3647060087778766207783379 5470590131668149311675069)
            ·
              refine ⟨2051471299375555991878151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5470590131668149311675069 2051471299375555991878151)
              ·
                refine ⟨3077206949063333987817227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2051471299375555991878151 3077206949063333987817227)
                ·
                  refine ⟨4615810423595000981725841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3077206949063333987817227 4615810423595000981725841)
                  ·
                    refine ⟨3461857817696250736294381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4615810423595000981725841 3461857817696250736294381)
                    ·
                      refine ⟨1298196681636094026110393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3461857817696250736294381 1298196681636094026110393)
                      ·
                        rfl

theorem cell23_2528229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_2528229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2528229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2528229 prefixEnd_2528229 := by exact prefixLift 2528229
  have htrace : WordTrace (prefixWord ++ tailWord_2528229) baseStart_2528229 baseEnd_2528229 := by
    simpa [prefixWord, tailWord_2528229, baseEnd_2528229] using wordTrace_append hprefix tailTrace_2528229
  have hstable : (prefixWord ++ tailWord_2528229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528229).length < 2 ^ (prefixWord ++ tailWord_2528229).sum := by decide
  have hdescent : baseEnd_2528229 < baseStart_2528229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528248 : List Nat := [2, 1, 2, 1, 1, 3, 1, 1, 5, 4, 2]
def baseStart_2528248 : Nat := 118140960795 + 2528248 * 2 ^ 59
def prefixEnd_2528248 : Nat := 4983230072969 + 3 ^ 40 * 2528248 * 2
def baseEnd_2528248 : Nat := 1298206437768529451772805

theorem tailTrace_2528248 : CollatzResearch.WordTrace tailWord_2528248 prefixEnd_2528248 1298206437768529451772805 := by
  unfold tailWord_2528248
  simp only [CollatzResearch.WordTrace]
  refine ⟨46106390072298380613460699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61475186763064507484614265 46106390072298380613460699)
  ·
    refine ⟨69159585108447570920191049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46106390072298380613460699 69159585108447570920191049)
    ·
      refine ⟨51869688831335678190143287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69159585108447570920191049 51869688831335678190143287)
      ·
        refine ⟨77804533247003517285214931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51869688831335678190143287 77804533247003517285214931)
        ·
          refine ⟨116706799870505275927822397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77804533247003517285214931 116706799870505275927822397)
          ·
            refine ⟨43765049951439478472933399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116706799870505275927822397 43765049951439478472933399)
            ·
              refine ⟨65647574927159217709400099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43765049951439478472933399 65647574927159217709400099)
              ·
                refine ⟨98471362390738826564100149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65647574927159217709400099 98471362390738826564100149)
                ·
                  refine ⟨9231690224131764990384389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 98471362390738826564100149 9231690224131764990384389)
                  ·
                    refine ⟨1730941917024705935697073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9231690224131764990384389 1730941917024705935697073)
                    ·
                      refine ⟨1298206437768529451772805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1730941917024705935697073 1298206437768529451772805)
                      ·
                        rfl

theorem cell23_2528248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 5, 4, 2].length) (baseStart_2528248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2528248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2528248 prefixEnd_2528248 := by exact prefixLift 2528248
  have htrace : WordTrace (prefixWord ++ tailWord_2528248) baseStart_2528248 baseEnd_2528248 := by
    simpa [prefixWord, tailWord_2528248, baseEnd_2528248] using wordTrace_append hprefix tailTrace_2528248
  have hstable : (prefixWord ++ tailWord_2528248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528248).length < 2 ^ (prefixWord ++ tailWord_2528248).sum := by decide
  have hdescent : baseEnd_2528248 < baseStart_2528248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528295 : List Nat := [1, 1, 7, 1, 1, 1, 1, 2, 2, 2, 4]
def baseStart_2528295 : Nat := 118140960795 + 2528295 * 2 ^ 59
def prefixEnd_2528295 : Nat := 4983230072969 + 3 ^ 40 * 2528295 * 2
def baseEnd_2528295 : Nat := 1298230571359290767885089

theorem tailTrace_2528295 : CollatzResearch.WordTrace tailWord_2528295 prefixEnd_2528295 1298230571359290767885089 := by
  unfold tailWord_2528295
  simp only [CollatzResearch.WordTrace]
  refine ⟨92214494375426488253882339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61476329583617658835921559 92214494375426488253882339)
  ·
    refine ⟨138321741563139732380823509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92214494375426488253882339 138321741563139732380823509)
    ·
      refine ⟨3241915817886087477675551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 138321741563139732380823509 3241915817886087477675551)
      ·
        refine ⟨4862873726829131216513327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3241915817886087477675551 4862873726829131216513327)
        ·
          refine ⟨7294310590243696824769991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4862873726829131216513327 7294310590243696824769991)
          ·
            refine ⟨10941465885365545237154987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7294310590243696824769991 10941465885365545237154987)
            ·
              refine ⟨16412198828048317855732481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10941465885365545237154987 16412198828048317855732481)
              ·
                refine ⟨12309149121036238391799361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16412198828048317855732481 12309149121036238391799361)
                ·
                  refine ⟨9231861840777178793849521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12309149121036238391799361 9231861840777178793849521)
                  ·
                    refine ⟨6923896380582884095387141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9231861840777178793849521 6923896380582884095387141)
                    ·
                      refine ⟨1298230571359290767885089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6923896380582884095387141 1298230571359290767885089)
                      ·
                        rfl

theorem cell23_2528295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_2528295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2528295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2528295 prefixEnd_2528295 := by exact prefixLift 2528295
  have htrace : WordTrace (prefixWord ++ tailWord_2528295) baseStart_2528295 baseEnd_2528295 := by
    simpa [prefixWord, tailWord_2528295, baseEnd_2528295] using wordTrace_append hprefix tailTrace_2528295
  have hstable : (prefixWord ++ tailWord_2528295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528295).length < 2 ^ (prefixWord ++ tailWord_2528295).sum := by decide
  have hdescent : baseEnd_2528295 < baseStart_2528295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528311 : List Nat := [1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 7]
def baseStart_2528311 : Nat := 118140960795 + 2528311 * 2 ^ 59
def prefixEnd_2528311 : Nat := 4983230072969 + 3 ^ 40 * 2528311 * 2
def baseEnd_2528311 : Nat := 1298238787049762705285015

theorem tailTrace_2528311 : CollatzResearch.WordTrace tailWord_2528311 prefixEnd_2528311 1298238787049762705285015 := by
  unfold tailWord_2528311
  simp only [CollatzResearch.WordTrace]
  refine ⟨92215077943368522986464787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61476718628912348657643191 92215077943368522986464787)
  ·
    refine ⟨138322616915052784479697181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92215077943368522986464787 138322616915052784479697181)
    ·
      refine ⟨51870981343144794179886443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138322616915052784479697181 51870981343144794179886443)
      ·
        refine ⟨77806472014717191269829665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51870981343144794179886443 77806472014717191269829665)
        ·
          refine ⟨58354854011037893452372249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77806472014717191269829665 58354854011037893452372249)
          ·
            refine ⟨43766140508278420089279187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58354854011037893452372249 43766140508278420089279187)
            ·
              refine ⟨65649210762417630133918781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43766140508278420089279187 65649210762417630133918781)
              ·
                refine ⟨24618454035906611300219543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65649210762417630133918781 24618454035906611300219543)
                ·
                  refine ⟨36927681053859916950329315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24618454035906611300219543 36927681053859916950329315)
                  ·
                    refine ⟨55391521580789875425493973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36927681053859916950329315 55391521580789875425493973)
                    ·
                      refine ⟨1298238787049762705285015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 55391521580789875425493973 1298238787049762705285015)
                      ·
                        rfl

theorem cell23_2528311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 7].length) (baseStart_2528311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2528311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2528311 prefixEnd_2528311 := by exact prefixLift 2528311
  have htrace : WordTrace (prefixWord ++ tailWord_2528311) baseStart_2528311 baseEnd_2528311 := by
    simpa [prefixWord, tailWord_2528311, baseEnd_2528311] using wordTrace_append hprefix tailTrace_2528311
  have hstable : (prefixWord ++ tailWord_2528311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528311).length < 2 ^ (prefixWord ++ tailWord_2528311).sum := by decide
  have hdescent : baseEnd_2528311 < baseStart_2528311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528405 : List Nat := [1, 3, 2, 1, 1, 1, 2, 1, 7, 1, 3]
def baseStart_2528405 : Nat := 118140960795 + 2528405 * 2 ^ 59
def prefixEnd_2528405 : Nat := 4983230072969 + 3 ^ 40 * 2528405 * 2
def baseEnd_2528405 : Nat := 1298287054231285337509583

theorem tailTrace_2528405 : CollatzResearch.WordTrace tailWord_2528405 prefixEnd_2528405 1298287054231285337509583 := by
  unfold tailWord_2528405
  simp only [CollatzResearch.WordTrace]
  refine ⟨92218506405027977040386669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61479004270018651360257779 92218506405027977040386669)
  ·
    refine ⟨34581939901885491390145001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92218506405027977040386669 34581939901885491390145001)
    ·
      refine ⟨25936454926414118542608751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34581939901885491390145001 25936454926414118542608751)
      ·
        refine ⟨38904682389621177813913127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25936454926414118542608751 38904682389621177813913127)
        ·
          refine ⟨58357023584431766720869691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38904682389621177813913127 58357023584431766720869691)
          ·
            refine ⟨87535535376647650081304537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58357023584431766720869691 87535535376647650081304537)
            ·
              refine ⟨65651651532485737560978403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87535535376647650081304537 65651651532485737560978403)
              ·
                refine ⟨98477477298728606341467605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65651651532485737560978403 98477477298728606341467605)
                ·
                  refine ⟨2308065874188951711128147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 98477477298728606341467605 2308065874188951711128147)
                  ·
                    refine ⟨3462098811283427566692221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2308065874188951711128147 3462098811283427566692221)
                    ·
                      refine ⟨1298287054231285337509583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3462098811283427566692221 1298287054231285337509583)
                      ·
                        rfl

theorem cell23_2528405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 7, 1, 3].length) (baseStart_2528405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2528405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2528405 prefixEnd_2528405 := by exact prefixLift 2528405
  have htrace : WordTrace (prefixWord ++ tailWord_2528405) baseStart_2528405 baseEnd_2528405 := by
    simpa [prefixWord, tailWord_2528405, baseEnd_2528405] using wordTrace_append hprefix tailTrace_2528405
  have hstable : (prefixWord ++ tailWord_2528405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528405).length < 2 ^ (prefixWord ++ tailWord_2528405).sum := by decide
  have hdescent : baseEnd_2528405 < baseStart_2528405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528445 : List Nat := [1, 4, 1, 2, 1, 1, 4, 1, 3, 1, 4]
def baseStart_2528445 : Nat := 118140960795 + 2528445 * 2 ^ 59
def prefixEnd_2528445 : Nat := 4983230072969 + 3 ^ 40 * 2528445 * 2
def baseEnd_2528445 : Nat := 1298307593457465181009399

theorem tailTrace_2528445 : CollatzResearch.WordTrace tailWord_2528445 prefixEnd_2528445 1298307593457465181009399 := by
  unfold tailWord_2528445
  simp only [CollatzResearch.WordTrace]
  refine ⟨92219965324883063871842789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61479976883255375914561859 92219965324883063871842789)
  ·
    refine ⟨17291243498415574475970523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92219965324883063871842789 17291243498415574475970523)
    ·
      refine ⟨25936865247623361713955785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17291243498415574475970523 25936865247623361713955785)
      ·
        refine ⟨19452648935717521285466839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25936865247623361713955785 19452648935717521285466839)
        ·
          refine ⟨29178973403576281928200259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19452648935717521285466839 29178973403576281928200259)
          ·
            refine ⟨43768460105364422892300389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29178973403576281928200259 43768460105364422892300389)
            ·
              refine ⟨8206586269755829292306323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43768460105364422892300389 8206586269755829292306323)
              ·
                refine ⟨12309879404633743938459485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8206586269755829292306323 12309879404633743938459485)
                ·
                  refine ⟨4616204776737653976922307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12309879404633743938459485 4616204776737653976922307)
                  ·
                    refine ⟨6924307165106480965383461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4616204776737653976922307 6924307165106480965383461)
                    ·
                      refine ⟨1298307593457465181009399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6924307165106480965383461 1298307593457465181009399)
                      ·
                        rfl

theorem cell23_2528445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_2528445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2528445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2528445 prefixEnd_2528445 := by exact prefixLift 2528445
  have htrace : WordTrace (prefixWord ++ tailWord_2528445) baseStart_2528445 baseEnd_2528445 := by
    simpa [prefixWord, tailWord_2528445, baseEnd_2528445] using wordTrace_append hprefix tailTrace_2528445
  have hstable : (prefixWord ++ tailWord_2528445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528445).length < 2 ^ (prefixWord ++ tailWord_2528445).sum := by decide
  have hdescent : baseEnd_2528445 < baseStart_2528445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528449 : List Nat := [1, 2, 6, 1, 1, 2, 1, 1, 1, 5, 2]
def baseStart_2528449 : Nat := 118140960795 + 2528449 * 2 ^ 59
def prefixEnd_2528449 : Nat := 4983230072969 + 3 ^ 40 * 2528449 * 2
def baseEnd_2528449 : Nat := 1298309647380083165359381

theorem tailTrace_2528449 : CollatzResearch.WordTrace tailWord_2528449 prefixEnd_2528449 1298309647380083165359381 := by
  unfold tailWord_2528449
  simp only [CollatzResearch.WordTrace]
  refine ⟨92220111216868572554988401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61480074144579048369992267 92220111216868572554988401)
  ·
    refine ⟨69165083412651429416241301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92220111216868572554988401 69165083412651429416241301)
    ·
      refine ⟨3242113284968035753886311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 69165083412651429416241301 3242113284968035753886311)
      ·
        refine ⟨4863169927452053630829467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3242113284968035753886311 4863169927452053630829467)
        ·
          refine ⟨7294754891178080446244201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4863169927452053630829467 7294754891178080446244201)
          ·
            refine ⟨5471066168383560334683151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7294754891178080446244201 5471066168383560334683151)
            ·
              refine ⟨8206599252575340502024727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5471066168383560334683151 8206599252575340502024727)
              ·
                refine ⟨12309898878863010753037091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8206599252575340502024727 12309898878863010753037091)
                ·
                  refine ⟨18464848318294516129555637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12309898878863010753037091 18464848318294516129555637)
                  ·
                    refine ⟨1731079529840110887145841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18464848318294516129555637 1731079529840110887145841)
                    ·
                      refine ⟨1298309647380083165359381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1731079529840110887145841 1298309647380083165359381)
                      ·
                        rfl

theorem cell23_2528449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_2528449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2528449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2528449 prefixEnd_2528449 := by exact prefixLift 2528449
  have htrace : WordTrace (prefixWord ++ tailWord_2528449) baseStart_2528449 baseEnd_2528449 := by
    simpa [prefixWord, tailWord_2528449, baseEnd_2528449] using wordTrace_append hprefix tailTrace_2528449
  have hstable : (prefixWord ++ tailWord_2528449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528449).length < 2 ^ (prefixWord ++ tailWord_2528449).sum := by decide
  have hdescent : baseEnd_2528449 < baseStart_2528449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528472 : List Nat := [2, 1, 2, 2, 5, 1, 1, 1, 4, 4]
def baseStart_2528472 : Nat := 118140960795 + 2528472 * 2 ^ 59
def prefixEnd_2528472 : Nat := 4983230072969 + 3 ^ 40 * 2528472 * 2
def baseEnd_2528472 : Nat := 432773819145045525123925

theorem tailTrace_2528472 : CollatzResearch.WordTrace tailWord_2528472 prefixEnd_2528472 432773819145045525123925 := by
  unfold tailWord_2528472
  simp only [CollatzResearch.WordTrace]
  refine ⟨46110475047892623741537835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61480633397190164988717113 46110475047892623741537835)
  ·
    refine ⟨69165712571838935612306753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46110475047892623741537835 69165712571838935612306753)
    ·
      refine ⟨51874284428879201709230065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69165712571838935612306753 51874284428879201709230065)
      ·
        refine ⟨38905713321659401281922549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51874284428879201709230065 38905713321659401281922549)
        ·
          refine ⟨3647410623905568870180239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38905713321659401281922549 3647410623905568870180239)
          ·
            refine ⟨5471115935858353305270359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3647410623905568870180239 5471115935858353305270359)
            ·
              refine ⟨8206673903787529957905539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5471115935858353305270359 8206673903787529957905539)
              ·
                refine ⟨12310010855681294936858309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8206673903787529957905539 12310010855681294936858309)
                ·
                  refine ⟨2308127035440242800660933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12310010855681294936858309 2308127035440242800660933)
                  ·
                    refine ⟨432773819145045525123925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2308127035440242800660933 432773819145045525123925)
                    ·
                      rfl

theorem cell23_2528472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 4, 4].length) (baseStart_2528472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2528472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2528472 prefixEnd_2528472 := by exact prefixLift 2528472
  have htrace : WordTrace (prefixWord ++ tailWord_2528472) baseStart_2528472 baseEnd_2528472 := by
    simpa [prefixWord, tailWord_2528472, baseEnd_2528472] using wordTrace_append hprefix tailTrace_2528472
  have hstable : (prefixWord ++ tailWord_2528472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528472).length < 2 ^ (prefixWord ++ tailWord_2528472).sum := by decide
  have hdescent : baseEnd_2528472 < baseStart_2528472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528492 : List Nat := [2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 4]
def baseStart_2528492 : Nat := 118140960795 + 2528492 * 2 ^ 59
def prefixEnd_2528492 : Nat := 4983230072969 + 3 ^ 40 * 2528492 * 2
def baseEnd_2528492 : Nat := 1298331727048226497121683

theorem tailTrace_2528492 : CollatzResearch.WordTrace tailWord_2528492 prefixEnd_2528492 1298331727048226497121683 := by
  unfold tailWord_2528492
  simp only [CollatzResearch.WordTrace]
  refine ⟨46110839777856395449401865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61481119703808527265869153 46110839777856395449401865)
  ·
    refine ⟨34583129833392296587051399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46110839777856395449401865 34583129833392296587051399)
    ·
      refine ⟨51874694750088444880577099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34583129833392296587051399 51874694750088444880577099)
      ·
        refine ⟨77812042125132667320865649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51874694750088444880577099 77812042125132667320865649)
        ·
          refine ⟨58359031593849500490649237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77812042125132667320865649 58359031593849500490649237)
          ·
            refine ⟨2735579605961695335499183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 58359031593849500490649237 2735579605961695335499183)
            ·
              refine ⟨4103369408942543003248775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2735579605961695335499183 4103369408942543003248775)
              ·
                refine ⟨6155054113413814504873163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4103369408942543003248775 6155054113413814504873163)
                ·
                  refine ⟨9232581170120721757309745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6155054113413814504873163 9232581170120721757309745)
                  ·
                    refine ⟨6924435877590541317982309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9232581170120721757309745 6924435877590541317982309)
                    ·
                      refine ⟨1298331727048226497121683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6924435877590541317982309 1298331727048226497121683)
                      ·
                        rfl

theorem cell23_2528492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 4].length) (baseStart_2528492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2528492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2528492 prefixEnd_2528492 := by exact prefixLift 2528492
  have htrace : WordTrace (prefixWord ++ tailWord_2528492) baseStart_2528492 baseEnd_2528492 := by
    simpa [prefixWord, tailWord_2528492, baseEnd_2528492] using wordTrace_append hprefix tailTrace_2528492
  have hstable : (prefixWord ++ tailWord_2528492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528492).length < 2 ^ (prefixWord ++ tailWord_2528492).sum := by decide
  have hdescent : baseEnd_2528492 < baseStart_2528492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528513 : List Nat := [1, 2, 4, 1, 1, 5, 1, 3, 1, 2, 2]
def baseStart_2528513 : Nat := 118140960795 + 2528513 * 2 ^ 59
def prefixEnd_2528513 : Nat := 4983230072969 + 3 ^ 40 * 2528513 * 2
def baseEnd_2528513 : Nat := 1298342510141970914959087

theorem tailTrace_2528513 : CollatzResearch.WordTrace tailWord_2528513 prefixEnd_2528513 1298342510141970914959087 := by
  unfold tailWord_2528513
  simp only [CollatzResearch.WordTrace]
  refine ⟨92222445488636711485318193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61481630325757807656878795 92222445488636711485318193)
  ·
    refine ⟨69166834116477533613988645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92222445488636711485318193 69166834116477533613988645)
    ·
      refine ⟨12968781396839537552622871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69166834116477533613988645 12968781396839537552622871)
      ·
        refine ⟨19453172095259306328934307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12968781396839537552622871 19453172095259306328934307)
        ·
          refine ⟨29179758142888959493401461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19453172095259306328934307 29179758142888959493401461)
          ·
            refine ⟨2735602325895839952506387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29179758142888959493401461 2735602325895839952506387)
            ·
              refine ⟨4103403488843759928759581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2735602325895839952506387 4103403488843759928759581)
              ·
                refine ⟨1538776308316409973284843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4103403488843759928759581 1538776308316409973284843)
                ·
                  refine ⟨2308164462474614959927265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1538776308316409973284843 2308164462474614959927265)
                  ·
                    refine ⟨1731123346855961219945449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2308164462474614959927265 1731123346855961219945449)
                    ·
                      refine ⟨1298342510141970914959087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1731123346855961219945449 1298342510141970914959087)
                      ·
                        rfl

theorem cell23_2528513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 3, 1, 2, 2].length) (baseStart_2528513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2528513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2528513 prefixEnd_2528513 := by exact prefixLift 2528513
  have htrace : WordTrace (prefixWord ++ tailWord_2528513) baseStart_2528513 baseEnd_2528513 := by
    simpa [prefixWord, tailWord_2528513, baseEnd_2528513] using wordTrace_append hprefix tailTrace_2528513
  have hstable : (prefixWord ++ tailWord_2528513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528513).length < 2 ^ (prefixWord ++ tailWord_2528513).sum := by decide
  have hdescent : baseEnd_2528513 < baseStart_2528513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528522 : List Nat := [3, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2]
def baseStart_2528522 : Nat := 118140960795 + 2528522 * 2 ^ 59
def prefixEnd_2528522 : Nat := 4983230072969 + 3 ^ 40 * 2528522 * 2
def baseEnd_2528522 : Nat := 1298347131467861379746545

theorem tailTrace_2528522 : CollatzResearch.WordTrace tailWord_2528522 prefixEnd_2528522 1298347131467861379746545 := by
  unfold tailWord_2528522
  simp only [CollatzResearch.WordTrace]
  refine ⟨23055693436401026505598955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61481849163736070681597213 23055693436401026505598955)
  ·
    refine ⟨34583540154601539758398433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23055693436401026505598955 34583540154601539758398433)
    ·
      refine ⟨25937655115951154818798825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34583540154601539758398433 25937655115951154818798825)
      ·
        refine ⟨19453241336963366114099119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25937655115951154818798825 19453241336963366114099119)
        ·
          refine ⟨29179862005445049171148679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19453241336963366114099119 29179862005445049171148679)
          ·
            refine ⟨43769793008167573756723019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29179862005445049171148679 43769793008167573756723019)
            ·
              refine ⟨65654689512251360635084529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43769793008167573756723019 65654689512251360635084529)
              ·
                refine ⟨49241017134188520476313397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65654689512251360635084529 49241017134188520476313397)
                ·
                  refine ⟨4616345356330173794654381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49241017134188520476313397 4616345356330173794654381)
                  ·
                    refine ⟨1731129508623815172995393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4616345356330173794654381 1731129508623815172995393)
                    ·
                      refine ⟨1298347131467861379746545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1731129508623815172995393 1298347131467861379746545)
                      ·
                        rfl

theorem cell23_2528522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2].length) (baseStart_2528522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2528522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2528522 prefixEnd_2528522 := by exact prefixLift 2528522
  have htrace : WordTrace (prefixWord ++ tailWord_2528522) baseStart_2528522 baseEnd_2528522 := by
    simpa [prefixWord, tailWord_2528522, baseEnd_2528522] using wordTrace_append hprefix tailTrace_2528522
  have hstable : (prefixWord ++ tailWord_2528522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528522).length < 2 ^ (prefixWord ++ tailWord_2528522).sum := by decide
  have hdescent : baseEnd_2528522 < baseStart_2528522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528530 : List Nat := [3, 2, 4, 2, 1, 2, 1, 1, 3, 2, 2]
def baseStart_2528530 : Nat := 118140960795 + 2528530 * 2 ^ 59
def prefixEnd_2528530 : Nat := 4983230072969 + 3 ^ 40 * 2528530 * 2
def baseEnd_2528530 : Nat := 1298351239313097348446509

theorem tailTrace_2528530 : CollatzResearch.WordTrace tailWord_2528530 prefixEnd_2528530 1298351239313097348446509 := by
  unfold tailWord_2528530
  simp only [CollatzResearch.WordTrace]
  refine ⟨23055766382393780847171761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61482043686383415592458029 23055766382393780847171761)
  ·
    refine ⟨17291824786795335635378821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23055766382393780847171761 17291824786795335635378821)
    ·
      refine ⟨3242217147524125431633529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17291824786795335635378821 3242217147524125431633529)
      ·
        refine ⟨2431662860643094073725147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3242217147524125431633529 2431662860643094073725147)
        ·
          refine ⟨3647494290964641110587721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2431662860643094073725147 3647494290964641110587721)
          ·
            refine ⟨2735620718223480832940791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3647494290964641110587721 2735620718223480832940791)
            ·
              refine ⟨4103431077335221249411187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2735620718223480832940791 4103431077335221249411187)
              ·
                refine ⟨6155146616002831874116781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4103431077335221249411187 6155146616002831874116781)
                ·
                  refine ⟨2308179981001061952793793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6155146616002831874116781 2308179981001061952793793)
                  ·
                    refine ⟨1731134985750796464595345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2308179981001061952793793 1731134985750796464595345)
                    ·
                      refine ⟨1298351239313097348446509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1731134985750796464595345 1298351239313097348446509)
                      ·
                        rfl

theorem cell23_2528530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_2528530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2528530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2528530 prefixEnd_2528530 := by exact prefixLift 2528530
  have htrace : WordTrace (prefixWord ++ tailWord_2528530) baseStart_2528530 baseEnd_2528530 := by
    simpa [prefixWord, tailWord_2528530, baseEnd_2528530] using wordTrace_append hprefix tailTrace_2528530
  have hstable : (prefixWord ++ tailWord_2528530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528530).length < 2 ^ (prefixWord ++ tailWord_2528530).sum := by decide
  have hdescent : baseEnd_2528530 < baseStart_2528530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528535 : List Nat := [1, 1, 3, 4, 1, 1, 2, 1, 2, 3, 4]
def baseStart_2528535 : Nat := 118140960795 + 2528535 * 2 ^ 59
def prefixEnd_2528535 : Nat := 4983230072969 + 3 ^ 40 * 2528535 * 2
def baseEnd_2528535 : Nat := 1298353806716369828883985

theorem tailTrace_2528535 : CollatzResearch.WordTrace tailWord_2528535 prefixEnd_2528535 1298353806716369828883985 := by
  unfold tailWord_2528535
  simp only [CollatzResearch.WordTrace]
  refine ⟨92223247894557009242619059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61482165263038006161746039 92223247894557009242619059)
  ·
    refine ⟨138334871841835513863928589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92223247894557009242619059 138334871841835513863928589)
    ·
      refine ⟨51875576940688317698973221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138334871841835513863928589 51875576940688317698973221)
      ·
        refine ⟨9726670676379059568557479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51875576940688317698973221 9726670676379059568557479)
        ·
          refine ⟨14590006014568589352836219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9726670676379059568557479 14590006014568589352836219)
          ·
            refine ⟨21885009021852884029254329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14590006014568589352836219 21885009021852884029254329)
            ·
              refine ⟨16413756766389663021940747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21885009021852884029254329 16413756766389663021940747)
              ·
                refine ⟨24620635149584494532911121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16413756766389663021940747 24620635149584494532911121)
                ·
                  refine ⟨18465476362188370899683341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24620635149584494532911121 18465476362188370899683341)
                  ·
                    refine ⟨6924553635820639087381253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18465476362188370899683341 6924553635820639087381253)
                    ·
                      refine ⟨1298353806716369828883985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6924553635820639087381253 1298353806716369828883985)
                      ·
                        rfl

theorem cell23_2528535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_2528535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2528535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2528535 prefixEnd_2528535 := by exact prefixLift 2528535
  have htrace : WordTrace (prefixWord ++ tailWord_2528535) baseStart_2528535 baseEnd_2528535 := by
    simpa [prefixWord, tailWord_2528535, baseEnd_2528535] using wordTrace_append hprefix tailTrace_2528535
  have hstable : (prefixWord ++ tailWord_2528535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528535).length < 2 ^ (prefixWord ++ tailWord_2528535).sum := by decide
  have hdescent : baseEnd_2528535 < baseStart_2528535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528546 : List Nat := [3, 3, 1, 1, 4, 1, 1, 3, 2, 1, 3]
def baseStart_2528546 : Nat := 118140960795 + 2528546 * 2 ^ 59
def prefixEnd_2528546 : Nat := 4983230072969 + 3 ^ 40 * 2528546 * 2
def baseEnd_2528546 : Nat := 1298359455003569285846435

theorem tailTrace_2528546 : CollatzResearch.WordTrace tailWord_2528546 prefixEnd_2528546 1298359455003569285846435 := by
  unfold tailWord_2528546
  simp only [CollatzResearch.WordTrace]
  refine ⟨23055912274379289530317373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61482432731678105414179661 23055912274379289530317373)
  ·
    refine ⟨8645967102892233573869015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23055912274379289530317373 8645967102892233573869015)
    ·
      refine ⟨12968950654338350360803523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8645967102892233573869015 12968950654338350360803523)
      ·
        refine ⟨19453425981507525541205285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12968950654338350360803523 19453425981507525541205285)
        ·
          refine ⟨3647517371532661038975991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19453425981507525541205285 3647517371532661038975991)
          ·
            refine ⟨5471276057298991558463987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3647517371532661038975991 5471276057298991558463987)
            ·
              refine ⟨8206914085948487337695981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5471276057298991558463987 8206914085948487337695981)
              ·
                refine ⟨3077592782230682751635993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8206914085948487337695981 3077592782230682751635993)
                ·
                  refine ⟨2308194586673012063726995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3077592782230682751635993 2308194586673012063726995)
                  ·
                    refine ⟨3462291880009518095590493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2308194586673012063726995 3462291880009518095590493)
                    ·
                      refine ⟨1298359455003569285846435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3462291880009518095590493 1298359455003569285846435)
                      ·
                        rfl

theorem cell23_2528546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 3, 2, 1, 3].length) (baseStart_2528546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2528546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2528546 prefixEnd_2528546 := by exact prefixLift 2528546
  have htrace : WordTrace (prefixWord ++ tailWord_2528546) baseStart_2528546 baseEnd_2528546 := by
    simpa [prefixWord, tailWord_2528546, baseEnd_2528546] using wordTrace_append hprefix tailTrace_2528546
  have hstable : (prefixWord ++ tailWord_2528546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528546).length < 2 ^ (prefixWord ++ tailWord_2528546).sum := by decide
  have hdescent : baseEnd_2528546 < baseStart_2528546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528592 : List Nat := [2, 1, 1, 1, 1, 5, 3, 4, 5]
def baseStart_2528592 : Nat := 118140960795 + 2528592 * 2 ^ 59
def prefixEnd_2528592 : Nat := 4983230072969 + 3 ^ 40 * 2528592 * 2
def baseEnd_2528592 : Nat := 144264786123741789541247

theorem tailTrace_2528592 : CollatzResearch.WordTrace tailWord_2528592 prefixEnd_2528592 144264786123741789541247 := by
  unfold tailWord_2528592
  simp only [CollatzResearch.WordTrace]
  refine ⟨46112663427675253988722015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61483551236900338651629353 46112663427675253988722015)
  ·
    refine ⟨69168995141512880983083023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46112663427675253988722015 69168995141512880983083023)
    ·
      refine ⟨103753492712269321474624535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69168995141512880983083023 103753492712269321474624535)
      ·
        refine ⟨155630239068403982211936803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103753492712269321474624535 155630239068403982211936803)
        ·
          refine ⟨233445358602605973317905205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155630239068403982211936803 233445358602605973317905205)
          ·
            refine ⟨21885502368994309998553613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 233445358602605973317905205 21885502368994309998553613)
            ·
              refine ⟨8207063388372866249457605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21885502368994309998553613 8207063388372866249457605)
              ·
                refine ⟨1538824385319912421773301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8207063388372866249457605 1538824385319912421773301)
                ·
                  refine ⟨144264786123741789541247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1538824385319912421773301 144264786123741789541247)
                  ·
                    rfl

theorem cell23_2528592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 4, 5].length) (baseStart_2528592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2528592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2528592 prefixEnd_2528592 := by exact prefixLift 2528592
  have htrace : WordTrace (prefixWord ++ tailWord_2528592) baseStart_2528592 baseEnd_2528592 := by
    simpa [prefixWord, tailWord_2528592, baseEnd_2528592] using wordTrace_append hprefix tailTrace_2528592
  have hstable : (prefixWord ++ tailWord_2528592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528592).length < 2 ^ (prefixWord ++ tailWord_2528592).sum := by decide
  have hdescent : baseEnd_2528592 < baseStart_2528592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528645 : List Nat := [1, 3, 1, 1, 3, 1, 2, 1, 2, 3, 5]
def baseStart_2528645 : Nat := 118140960795 + 2528645 * 2 ^ 59
def prefixEnd_2528645 : Nat := 4983230072969 + 3 ^ 40 * 2528645 * 2
def baseEnd_2528645 : Nat := 1298410289588364398508479

theorem tailTrace_2528645 : CollatzResearch.WordTrace tailWord_2528645 prefixEnd_2528645 1298410289588364398508479 := by
  unfold tailWord_2528645
  simp only [CollatzResearch.WordTrace]
  refine ⟨92227259924158498029123389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61484839949438998686082259 92227259924158498029123389)
  ·
    refine ⟨34585222471559436760921271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92227259924158498029123389 34585222471559436760921271)
    ·
      refine ⟨51877833707339155141381907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34585222471559436760921271 51877833707339155141381907)
      ·
        refine ⟨77816750561008732712072861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51877833707339155141381907 77816750561008732712072861)
        ·
          refine ⟨29181281460378274767027323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77816750561008732712072861 29181281460378274767027323)
          ·
            refine ⟨43771922190567412150540985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29181281460378274767027323 43771922190567412150540985)
            ·
              refine ⟨32828941642925559112905739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43771922190567412150540985 32828941642925559112905739)
              ·
                refine ⟨49243412464388338669358609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32828941642925559112905739 49243412464388338669358609)
                ·
                  refine ⟨36932559348291254002018957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49243412464388338669358609 36932559348291254002018957)
                  ·
                    refine ⟨13849709755609220250757109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36932559348291254002018957 13849709755609220250757109)
                    ·
                      refine ⟨1298410289588364398508479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13849709755609220250757109 1298410289588364398508479)
                      ·
                        rfl

theorem cell23_2528645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 3, 5].length) (baseStart_2528645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2528645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2528645 prefixEnd_2528645 := by exact prefixLift 2528645
  have htrace : WordTrace (prefixWord ++ tailWord_2528645) baseStart_2528645 baseEnd_2528645 := by
    simpa [prefixWord, tailWord_2528645, baseEnd_2528645] using wordTrace_append hprefix tailTrace_2528645
  have hstable : (prefixWord ++ tailWord_2528645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528645).length < 2 ^ (prefixWord ++ tailWord_2528645).sum := by decide
  have hdescent : baseEnd_2528645 < baseStart_2528645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528669 : List Nat := [1, 4, 2, 1, 3, 1, 2, 2, 3, 4]
def baseStart_2528669 : Nat := 118140960795 + 2528669 * 2 ^ 59
def prefixEnd_2528669 : Nat := 4983230072969 + 3 ^ 40 * 2528669 * 2
def baseEnd_2528669 : Nat := 432807537708024101536123

theorem tailTrace_2528669 : CollatzResearch.WordTrace tailWord_2528669 prefixEnd_2528669 432807537708024101536123 := by
  unfold tailWord_2528669
  simp only [CollatzResearch.WordTrace]
  refine ⟨92228135276071550127997061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61485423517381033418664707 92228135276071550127997061)
  ·
    refine ⟨17292775364263415648999449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92228135276071550127997061 17292775364263415648999449)
    ·
      refine ⟨12969581523197561736749587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17292775364263415648999449 12969581523197561736749587)
      ·
        refine ⟨19454372284796342605124381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12969581523197561736749587 19454372284796342605124381)
        ·
          refine ⟨7295389606798628476921643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19454372284796342605124381 7295389606798628476921643)
          ·
            refine ⟨10943084410197942715382465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7295389606798628476921643 10943084410197942715382465)
            ·
              refine ⟨8207313307648457036536849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10943084410197942715382465 8207313307648457036536849)
              ·
                refine ⟨6155484980736342777402637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8207313307648457036536849 6155484980736342777402637)
                ·
                  refine ⟨2308306867776128541525989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6155484980736342777402637 2308306867776128541525989)
                  ·
                    refine ⟨432807537708024101536123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2308306867776128541525989 432807537708024101536123)
                    ·
                      rfl

theorem cell23_2528669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_2528669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2528669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2528669 prefixEnd_2528669 := by exact prefixLift 2528669
  have htrace : WordTrace (prefixWord ++ tailWord_2528669) baseStart_2528669 baseEnd_2528669 := by
    simpa [prefixWord, tailWord_2528669, baseEnd_2528669] using wordTrace_append hprefix tailTrace_2528669
  have hstable : (prefixWord ++ tailWord_2528669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528669).length < 2 ^ (prefixWord ++ tailWord_2528669).sum := by decide
  have hdescent : baseEnd_2528669 < baseStart_2528669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528679 : List Nat := [1, 1, 6, 1, 1, 1, 2, 3, 2, 2, 3]
def baseStart_2528679 : Nat := 118140960795 + 2528679 * 2 ^ 59
def prefixEnd_2528679 : Nat := 4983230072969 + 3 ^ 40 * 2528679 * 2
def baseEnd_2528679 : Nat := 1298427747930617265483323

theorem tailTrace_2528679 : CollatzResearch.WordTrace tailWord_2528679 prefixEnd_2528679 1298427747930617265483323 := by
  unfold tailWord_2528679
  simp only [CollatzResearch.WordTrace]
  refine ⟨92228500006035321835861091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61485666670690214557240727 92228500006035321835861091)
  ·
    refine ⟨138342750009052982753791637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92228500006035321835861091 138342750009052982753791637)
    ·
      refine ⟨6484816406674358566583983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 138342750009052982753791637 6484816406674358566583983)
      ·
        refine ⟨9727224610011537849875975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6484816406674358566583983 9727224610011537849875975)
        ·
          refine ⟨14590836915017306774813963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9727224610011537849875975 14590836915017306774813963)
          ·
            refine ⟨21886255372525960162220945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14590836915017306774813963 21886255372525960162220945)
            ·
              refine ⟨16414691529394470121665709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21886255372525960162220945 16414691529394470121665709)
              ·
                refine ⟨6155509323522926295624641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16414691529394470121665709 6155509323522926295624641)
                ·
                  refine ⟨4616631992642194721718481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6155509323522926295624641 4616631992642194721718481)
                  ·
                    refine ⟨3462473994481646041288861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4616631992642194721718481 3462473994481646041288861)
                    ·
                      refine ⟨1298427747930617265483323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3462473994481646041288861 1298427747930617265483323)
                      ·
                        rfl

theorem cell23_2528679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_2528679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2528679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2528679 prefixEnd_2528679 := by exact prefixLift 2528679
  have htrace : WordTrace (prefixWord ++ tailWord_2528679) baseStart_2528679 baseEnd_2528679 := by
    simpa [prefixWord, tailWord_2528679, baseEnd_2528679] using wordTrace_append hprefix tailTrace_2528679
  have hstable : (prefixWord ++ tailWord_2528679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528679).length < 2 ^ (prefixWord ++ tailWord_2528679).sum := by decide
  have hdescent : baseEnd_2528679 < baseStart_2528679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528712 : List Nat := [2, 1, 3, 1, 3, 1, 2, 2, 3, 5]
def baseStart_2528712 : Nat := 118140960795 + 2528712 * 2 ^ 59
def prefixEnd_2528712 : Nat := 4983230072969 + 3 ^ 40 * 2528712 * 2
def baseEnd_2528712 : Nat := 432814897597405212123557

theorem tailTrace_2528712 : CollatzResearch.WordTrace tailWord_2528712 prefixEnd_2528712 432814897597405212123557 := by
  unfold tailWord_2528712
  simp only [CollatzResearch.WordTrace]
  refine ⟨46114851807457884235906195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61486469076610512314541593 46114851807457884235906195)
  ·
    refine ⟨69172277711186826353859293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46114851807457884235906195 69172277711186826353859293)
    ·
      refine ⟨25939604141695059882697235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69172277711186826353859293 25939604141695059882697235)
      ·
        refine ⟨38909406212542589824045853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25939604141695059882697235 38909406212542589824045853)
        ·
          refine ⟨14591027329703471184017195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38909406212542589824045853 14591027329703471184017195)
          ·
            refine ⟨21886540994555206776025793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14591027329703471184017195 21886540994555206776025793)
            ·
              refine ⟨16414905745916405082019345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21886540994555206776025793 16414905745916405082019345)
              ·
                refine ⟨12311179309437303811514509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16414905745916405082019345 12311179309437303811514509)
                ·
                  refine ⟨4616692241038988929317941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12311179309437303811514509 4616692241038988929317941)
                  ·
                    refine ⟨432814897597405212123557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4616692241038988929317941 432814897597405212123557)
                    ·
                      rfl

theorem cell23_2528712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 3, 5].length) (baseStart_2528712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2528712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2528712 prefixEnd_2528712 := by exact prefixLift 2528712
  have htrace : WordTrace (prefixWord ++ tailWord_2528712) baseStart_2528712 baseEnd_2528712 := by
    simpa [prefixWord, tailWord_2528712, baseEnd_2528712] using wordTrace_append hprefix tailTrace_2528712
  have hstable : (prefixWord ++ tailWord_2528712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528712).length < 2 ^ (prefixWord ++ tailWord_2528712).sum := by decide
  have hdescent : baseEnd_2528712 < baseStart_2528712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528716 : List Nat := [2, 2, 1, 4, 2, 3, 2, 1, 6]
def baseStart_2528716 : Nat := 118140960795 + 2528716 * 2 ^ 59
def prefixEnd_2528716 : Nat := 4983230072969 + 3 ^ 40 * 2528716 * 2
def baseEnd_2528716 : Nat := 144271860746092624524517

theorem tailTrace_2528716 : CollatzResearch.WordTrace tailWord_2528716 prefixEnd_2528716 144271860746092624524517 := by
  unfold tailWord_2528716
  simp only [CollatzResearch.WordTrace]
  refine ⟨46114924753450638577479001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61486566337934184769972001 46114924753450638577479001)
  ·
    refine ⟨34586193565087978933109251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46114924753450638577479001 34586193565087978933109251)
    ·
      refine ⟨51879290347631968399663877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34586193565087978933109251 51879290347631968399663877)
      ·
        refine ⟨9727366940180994074936977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51879290347631968399663877 9727366940180994074936977)
        ·
          refine ⟨7295525205135745556202733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9727366940180994074936977 7295525205135745556202733)
          ·
            refine ⟨2735821951925904583576025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7295525205135745556202733 2735821951925904583576025)
            ·
              refine ⟨2051866463944428437682019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2735821951925904583576025 2051866463944428437682019)
              ·
                refine ⟨3077799695916642656523029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2051866463944428437682019 3077799695916642656523029)
                ·
                  refine ⟨144271860746092624524517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3077799695916642656523029 144271860746092624524517)
                  ·
                    rfl

theorem cell23_2528716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2, 1, 6].length) (baseStart_2528716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2528716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2528716 prefixEnd_2528716 := by exact prefixLift 2528716
  have htrace : WordTrace (prefixWord ++ tailWord_2528716) baseStart_2528716 baseEnd_2528716 := by
    simpa [prefixWord, tailWord_2528716, baseEnd_2528716] using wordTrace_append hprefix tailTrace_2528716
  have hstable : (prefixWord ++ tailWord_2528716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528716).length < 2 ^ (prefixWord ++ tailWord_2528716).sum := by decide
  have hdescent : baseEnd_2528716 < baseStart_2528716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528729 : List Nat := [1, 2, 1, 2, 4, 2, 3, 2, 1, 5]
def baseStart_2528729 : Nat := 118140960795 + 2528729 * 2 ^ 59
def prefixEnd_2528729 : Nat := 4983230072969 + 3 ^ 40 * 2528729 * 2
def baseEnd_2528729 : Nat := 432817807321114023286031

theorem tailTrace_2528729 : CollatzResearch.WordTrace tailWord_2528729 prefixEnd_2528729 432817807321114023286031 := by
  unfold tailWord_2528729
  simp only [CollatzResearch.WordTrace]
  refine ⟨92230323655854180375181241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61486882437236120250120827 92230323655854180375181241)
  ·
    refine ⟨69172742741890635281385931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92230323655854180375181241 69172742741890635281385931)
    ·
      refine ⟨103759114112835952922078897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69172742741890635281385931 103759114112835952922078897)
      ·
        refine ⟨77819335584626964691559173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103759114112835952922078897 77819335584626964691559173)
        ·
          refine ⟨14591125422117555879667345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77819335584626964691559173 14591125422117555879667345)
          ·
            refine ⟨10943344066588166909750509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14591125422117555879667345 10943344066588166909750509)
            ·
              refine ⟨4103754024970562591156441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10943344066588166909750509 4103754024970562591156441)
              ·
                refine ⟨3077815518727921943367331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4103754024970562591156441 3077815518727921943367331)
                ·
                  refine ⟨4616723278091882915050997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3077815518727921943367331 4616723278091882915050997)
                  ·
                    refine ⟨432817807321114023286031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4616723278091882915050997 432817807321114023286031)
                    ·
                      rfl

theorem cell23_2528729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 2, 1, 5].length) (baseStart_2528729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2528729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2528729 prefixEnd_2528729 := by exact prefixLift 2528729
  have htrace : WordTrace (prefixWord ++ tailWord_2528729) baseStart_2528729 baseEnd_2528729 := by
    simpa [prefixWord, tailWord_2528729, baseEnd_2528729] using wordTrace_append hprefix tailTrace_2528729
  have hstable : (prefixWord ++ tailWord_2528729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528729).length < 2 ^ (prefixWord ++ tailWord_2528729).sum := by decide
  have hdescent : baseEnd_2528729 < baseStart_2528729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528760 : List Nat := [2, 1, 2, 1, 1, 7, 2, 2, 1, 1, 3]
def baseStart_2528760 : Nat := 118140960795 + 2528760 * 2 ^ 59
def prefixEnd_2528760 : Nat := 4983230072969 + 3 ^ 40 * 2528760 * 2
def baseEnd_2528760 : Nat := 1298469339863631448570451

theorem tailTrace_2528760 : CollatzResearch.WordTrace tailWord_2528760 prefixEnd_2528760 1298469339863631448570451 := by
  unfold tailWord_2528760
  simp only [CollatzResearch.WordTrace]
  refine ⟨46115727159370936334779867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61487636212494581779706489 46115727159370936334779867)
  ·
    refine ⟨69173590739056404502169801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46115727159370936334779867 69173590739056404502169801)
    ·
      refine ⟨51880193054292303376627351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69173590739056404502169801 51880193054292303376627351)
      ·
        refine ⟨77820289581438455064941027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51880193054292303376627351 77820289581438455064941027)
        ·
          refine ⟨116730434372157682597411541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77820289581438455064941027 116730434372157682597411541)
          ·
            refine ⟨2735869555597445685876833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 116730434372157682597411541 2735869555597445685876833)
            ·
              refine ⟨2051902166698084264407625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2735869555597445685876833 2051902166698084264407625)
              ·
                refine ⟨1538926625023563198305719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2051902166698084264407625 1538926625023563198305719)
                ·
                  refine ⟨2308389937535344797458579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1538926625023563198305719 2308389937535344797458579)
                  ·
                    refine ⟨3462584906303017196187869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2308389937535344797458579 3462584906303017196187869)
                    ·
                      refine ⟨1298469339863631448570451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3462584906303017196187869 1298469339863631448570451)
                      ·
                        rfl

theorem cell23_2528760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2, 2, 1, 1, 3].length) (baseStart_2528760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2528760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2528760 prefixEnd_2528760 := by exact prefixLift 2528760
  have htrace : WordTrace (prefixWord ++ tailWord_2528760) baseStart_2528760 baseEnd_2528760 := by
    simpa [prefixWord, tailWord_2528760, baseEnd_2528760] using wordTrace_append hprefix tailTrace_2528760
  have hstable : (prefixWord ++ tailWord_2528760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528760).length < 2 ^ (prefixWord ++ tailWord_2528760).sum := by decide
  have hdescent : baseEnd_2528760 < baseStart_2528760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528762 : List Nat := [3, 1, 1, 1, 1, 2, 3, 2, 3, 2, 4]
def baseStart_2528762 : Nat := 118140960795 + 2528762 * 2 ^ 59
def prefixEnd_2528762 : Nat := 4983230072969 + 3 ^ 40 * 2528762 * 2
def baseEnd_2528762 : Nat := 1298470366824940440745441

theorem tailTrace_2528762 : CollatzResearch.WordTrace tailWord_2528762 prefixEnd_2528762 1298470366824940440745441 := by
  unfold tailWord_2528762
  simp only [CollatzResearch.WordTrace]
  refine ⟨23057881816183656752783135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61487684843156418007421693 23057881816183656752783135)
  ·
    refine ⟨34586822724275485129174703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23057881816183656752783135 34586822724275485129174703)
    ·
      refine ⟨51880234086413227693762055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34586822724275485129174703 51880234086413227693762055)
      ·
        refine ⟨77820351129619841540643083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51880234086413227693762055 77820351129619841540643083)
        ·
          refine ⟨116730526694429762310964625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77820351129619841540643083 116730526694429762310964625)
          ·
            refine ⟨87547895020822321733223469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116730526694429762310964625 87547895020822321733223469)
            ·
              refine ⟨32830460632808370649958801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87547895020822321733223469 32830460632808370649958801)
              ·
                refine ⟨24622845474606277987469101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32830460632808370649958801 24622845474606277987469101)
                ·
                  refine ⟨9233567052977354245300913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24622845474606277987469101 9233567052977354245300913)
                  ·
                    refine ⟨6925175289733015683975685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9233567052977354245300913 6925175289733015683975685)
                    ·
                      refine ⟨1298470366824940440745441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6925175289733015683975685 1298470366824940440745441)
                      ·
                        rfl

theorem cell23_2528762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 3, 2, 4].length) (baseStart_2528762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2528762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2528762 prefixEnd_2528762 := by exact prefixLift 2528762
  have htrace : WordTrace (prefixWord ++ tailWord_2528762) baseStart_2528762 baseEnd_2528762 := by
    simpa [prefixWord, tailWord_2528762, baseEnd_2528762] using wordTrace_append hprefix tailTrace_2528762
  have hstable : (prefixWord ++ tailWord_2528762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528762).length < 2 ^ (prefixWord ++ tailWord_2528762).sum := by decide
  have hdescent : baseEnd_2528762 < baseStart_2528762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528789 : List Nat := [1, 3, 2, 1, 3, 3, 3, 7]
def baseStart_2528789 : Nat := 118140960795 + 2528789 * 2 ^ 59
def prefixEnd_2528789 : Nat := 4983230072969 + 3 ^ 40 * 2528789 * 2
def baseEnd_2528789 : Nat := 48092008548244882781771

theorem tailTrace_2528789 : CollatzResearch.WordTrace tailWord_2528789 prefixEnd_2528789 48092008548244882781771 := by
  unfold tailWord_2528789
  simp only [CollatzResearch.WordTrace]
  refine ⟨92232512035636810622365421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61488341357091207081576947 92232512035636810622365421)
  ·
    refine ⟨34587192013363803983387033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92232512035636810622365421 34587192013363803983387033)
    ·
      refine ⟨25940394010022852987540275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34587192013363803983387033 25940394010022852987540275)
      ·
        refine ⟨38910591015034279481310413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25940394010022852987540275 38910591015034279481310413)
        ·
          refine ⟨14591471630637854805491405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38910591015034279481310413 14591471630637854805491405)
          ·
            refine ⟨5471801861489195552059277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14591471630637854805491405 5471801861489195552059277)
            ·
              refine ⟨2051925698058448332022229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5471801861489195552059277 2051925698058448332022229)
              ·
                refine ⟨48092008548244882781771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2051925698058448332022229 48092008548244882781771)
                ·
                  rfl

theorem cell23_2528789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3, 7].length) (baseStart_2528789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2528789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2528789 prefixEnd_2528789 := by exact prefixLift 2528789
  have htrace : WordTrace (prefixWord ++ tailWord_2528789) baseStart_2528789 baseEnd_2528789 := by
    simpa [prefixWord, tailWord_2528789, baseEnd_2528789] using wordTrace_append hprefix tailTrace_2528789
  have hstable : (prefixWord ++ tailWord_2528789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528789).length < 2 ^ (prefixWord ++ tailWord_2528789).sum := by decide
  have hdescent : baseEnd_2528789 < baseStart_2528789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528799 : List Nat := [1, 1, 2, 4, 1, 1, 4, 2, 1, 3, 3]
def baseStart_2528799 : Nat := 118140960795 + 2528799 * 2 ^ 59
def prefixEnd_2528799 : Nat := 4983230072969 + 3 ^ 40 * 2528799 * 2
def baseEnd_2528799 : Nat := 1298489365609156795982771

theorem tailTrace_2528799 : CollatzResearch.WordTrace tailWord_2528799 prefixEnd_2528799 1298489365609156795982771 := by
  unfold tailWord_2528799
  simp only [CollatzResearch.WordTrace]
  refine ⟨92232876765600582330229451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61488584510400388220152967 92232876765600582330229451)
  ·
    refine ⟨138349315148400873495344177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92232876765600582330229451 138349315148400873495344177)
    ·
      refine ⟨103761986361300655121508133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138349315148400873495344177 103761986361300655121508133)
      ·
        refine ⟨19455372442743872835282775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103761986361300655121508133 19455372442743872835282775)
        ·
          refine ⟨29183058664115809252924163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19455372442743872835282775 29183058664115809252924163)
          ·
            refine ⟨43774587996173713879386245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29183058664115809252924163 43774587996173713879386245)
            ·
              refine ⟨8207735249282571352384921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43774587996173713879386245 8207735249282571352384921)
              ·
                refine ⟨6155801436961928514288691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8207735249282571352384921 6155801436961928514288691)
                ·
                  refine ⟨9233702155442892771433037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6155801436961928514288691 9233702155442892771433037)
                  ·
                    refine ⟨3462638308291084789287389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9233702155442892771433037 3462638308291084789287389)
                    ·
                      refine ⟨1298489365609156795982771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3462638308291084789287389 1298489365609156795982771)
                      ·
                        rfl

theorem cell23_2528799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_2528799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2528799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2528799 prefixEnd_2528799 := by exact prefixLift 2528799
  have htrace : WordTrace (prefixWord ++ tailWord_2528799) baseStart_2528799 baseEnd_2528799 := by
    simpa [prefixWord, tailWord_2528799, baseEnd_2528799] using wordTrace_append hprefix tailTrace_2528799
  have hstable : (prefixWord ++ tailWord_2528799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528799).length < 2 ^ (prefixWord ++ tailWord_2528799).sum := by decide
  have hdescent : baseEnd_2528799 < baseStart_2528799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528800 : List Nat := [2, 1, 1, 6, 1, 1, 1, 5, 1, 2, 2]
def baseStart_2528800 : Nat := 118140960795 + 2528800 * 2 ^ 59
def prefixEnd_2528800 : Nat := 4983230072969 + 3 ^ 40 * 2528800 * 2
def baseEnd_2528800 : Nat := 1298489879089811292070267

theorem tailTrace_2528800 : CollatzResearch.WordTrace tailWord_2528800 prefixEnd_2528800 1298489879089811292070267 := by
  unfold tailWord_2528800
  simp only [CollatzResearch.WordTrace]
  refine ⟨46116456619298479750507927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61488608825731306334010569 46116456619298479750507927)
  ·
    refine ⟨69174684928947719625761891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46116456619298479750507927 69174684928947719625761891)
    ·
      refine ⟨103762027393421579438642837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69174684928947719625761891 103762027393421579438642837)
      ·
        refine ⟨4863845034066636536186383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 103762027393421579438642837 4863845034066636536186383)
        ·
          refine ⟨7295767551099954804279575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4863845034066636536186383 7295767551099954804279575)
          ·
            refine ⟨10943651326649932206419363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7295767551099954804279575 10943651326649932206419363)
            ·
              refine ⟨16415476989974898309629045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10943651326649932206419363 16415476989974898309629045)
              ·
                refine ⟨1538950967810146716527723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16415476989974898309629045 1538950967810146716527723)
                ·
                  refine ⟨2308426451715220074791585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1538950967810146716527723 2308426451715220074791585)
                  ·
                    refine ⟨1731319838786415056093689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2308426451715220074791585 1731319838786415056093689)
                    ·
                      refine ⟨1298489879089811292070267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1731319838786415056093689 1298489879089811292070267)
                      ·
                        rfl

theorem cell23_2528800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_2528800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2528800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2528800 prefixEnd_2528800 := by exact prefixLift 2528800
  have htrace : WordTrace (prefixWord ++ tailWord_2528800) baseStart_2528800 baseEnd_2528800 := by
    simpa [prefixWord, tailWord_2528800, baseEnd_2528800] using wordTrace_append hprefix tailTrace_2528800
  have hstable : (prefixWord ++ tailWord_2528800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528800).length < 2 ^ (prefixWord ++ tailWord_2528800).sum := by decide
  have hdescent : baseEnd_2528800 < baseStart_2528800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528889 : List Nat := [1, 2, 1, 3, 3, 1, 2, 1, 1, 5, 3]
def baseStart_2528889 : Nat := 118140960795 + 2528889 * 2 ^ 59
def prefixEnd_2528889 : Nat := 4983230072969 + 3 ^ 40 * 2528889 * 2
def baseEnd_2528889 : Nat := 1298535578868061443857357

theorem tailTrace_2528889 : CollatzResearch.WordTrace tailWord_2528889 prefixEnd_2528889 1298535578868061443857357 := by
  unfold tailWord_2528889
  simp only [CollatzResearch.WordTrace]
  refine ⟨92236159335274527701005721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61490772890183018467337147 92236159335274527701005721)
  ·
    refine ⟨69177119501455895775754291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92236159335274527701005721 69177119501455895775754291)
    ·
      refine ⟨103765679252183843663631437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69177119501455895775754291 103765679252183843663631437)
      ·
        refine ⟨38912129719568941373861789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103765679252183843663631437 38912129719568941373861789)
        ·
          refine ⟨14592048644838353015198171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38912129719568941373861789 14592048644838353015198171)
          ·
            refine ⟨21888072967257529522797257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14592048644838353015198171 21888072967257529522797257)
            ·
              refine ⟨16416054725443147142097943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21888072967257529522797257 16416054725443147142097943)
              ·
                refine ⟨24624082088164720713146915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16416054725443147142097943 24624082088164720713146915)
                ·
                  refine ⟨36936123132247081069720373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24624082088164720713146915 36936123132247081069720373)
                  ·
                    refine ⟨3462761543648163850286285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36936123132247081069720373 3462761543648163850286285)
                    ·
                      refine ⟨1298535578868061443857357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3462761543648163850286285 1298535578868061443857357)
                      ·
                        rfl

theorem cell23_2528889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 5, 3].length) (baseStart_2528889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2528889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2528889 prefixEnd_2528889 := by exact prefixLift 2528889
  have htrace : WordTrace (prefixWord ++ tailWord_2528889) baseStart_2528889 baseEnd_2528889 := by
    simpa [prefixWord, tailWord_2528889, baseEnd_2528889] using wordTrace_append hprefix tailTrace_2528889
  have hstable : (prefixWord ++ tailWord_2528889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528889).length < 2 ^ (prefixWord ++ tailWord_2528889).sum := by decide
  have hdescent : baseEnd_2528889 < baseStart_2528889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528919 : List Nat := [1, 1, 3, 3, 2, 2, 1, 2, 1, 2, 5]
def baseStart_2528919 : Nat := 118140960795 + 2528919 * 2 ^ 59
def prefixEnd_2528919 : Nat := 4983230072969 + 3 ^ 40 * 2528919 * 2
def baseEnd_2528919 : Nat := 1298550983287696326482219

theorem tailTrace_2528919 : CollatzResearch.WordTrace tailWord_2528919 prefixEnd_2528919 1298550983287696326482219 := by
  unfold tailWord_2528919
  simp only [CollatzResearch.WordTrace]
  refine ⟨92237253525165842824597811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61491502350110561883065207 92237253525165842824597811)
  ·
    refine ⟨138355880287748764236896717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92237253525165842824597811 138355880287748764236896717)
    ·
      refine ⟨51883455107905786588836269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138355880287748764236896717 51883455107905786588836269)
      ·
        refine ⟨19456295665464669970813601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51883455107905786588836269 19456295665464669970813601)
        ·
          refine ⟨14592221749098502478110201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19456295665464669970813601 14592221749098502478110201)
          ·
            refine ⟨10944166311823876858582651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14592221749098502478110201 10944166311823876858582651)
            ·
              refine ⟨16416249467735815287873977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10944166311823876858582651 16416249467735815287873977)
              ·
                refine ⟨12312187100801861465905483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16416249467735815287873977 12312187100801861465905483)
                ·
                  refine ⟨18468280651202792198858225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12312187100801861465905483 18468280651202792198858225)
                  ·
                    refine ⟨13851210488402094149143669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18468280651202792198858225 13851210488402094149143669)
                    ·
                      refine ⟨1298550983287696326482219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13851210488402094149143669 1298550983287696326482219)
                      ·
                        rfl

theorem cell23_2528919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_2528919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2528919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2528919 prefixEnd_2528919 := by exact prefixLift 2528919
  have htrace : WordTrace (prefixWord ++ tailWord_2528919) baseStart_2528919 baseEnd_2528919 := by
    simpa [prefixWord, tailWord_2528919, baseEnd_2528919] using wordTrace_append hprefix tailTrace_2528919
  have hstable : (prefixWord ++ tailWord_2528919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528919).length < 2 ^ (prefixWord ++ tailWord_2528919).sum := by decide
  have hdescent : baseEnd_2528919 < baseStart_2528919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528930 : List Nat := [3, 3, 1, 4, 1, 1, 1, 4, 5]
def baseStart_2528930 : Nat := 118140960795 + 2528930 * 2 ^ 59
def prefixEnd_2528930 : Nat := 4983230072969 + 3 ^ 40 * 2528930 * 2
def baseEnd_2528930 : Nat := 144284070174988420382741

theorem tailTrace_2528930 : CollatzResearch.WordTrace tailWord_2528930 prefixEnd_2528930 144284070174988420382741 := by
  unfold tailWord_2528930
  simp only [CollatzResearch.WordTrace]
  refine ⟨23059413682031497925812061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61491769818750661135498829 23059413682031497925812061)
  ·
    refine ⟨8647280130761811722179523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23059413682031497925812061 8647280130761811722179523)
    ·
      refine ⟨12970920196142717583269285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8647280130761811722179523 12970920196142717583269285)
      ·
        refine ⟨2432047536776759546862991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12970920196142717583269285 2432047536776759546862991)
        ·
          refine ⟨3648071305165139320294487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2432047536776759546862991 3648071305165139320294487)
          ·
            refine ⟨5472106957747708980441731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3648071305165139320294487 5472106957747708980441731)
            ·
              refine ⟨8208160436621563470662597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5472106957747708980441731 8208160436621563470662597)
              ·
                refine ⟨1539030081866543150749237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8208160436621563470662597 1539030081866543150749237)
                ·
                  refine ⟨144284070174988420382741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1539030081866543150749237 144284070174988420382741)
                  ·
                    rfl

theorem cell23_2528930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 4, 5].length) (baseStart_2528930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2528930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2528930 prefixEnd_2528930 := by exact prefixLift 2528930
  have htrace : WordTrace (prefixWord ++ tailWord_2528930) baseStart_2528930 baseEnd_2528930 := by
    simpa [prefixWord, tailWord_2528930, baseEnd_2528930] using wordTrace_append hprefix tailTrace_2528930
  have hstable : (prefixWord ++ tailWord_2528930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528930).length < 2 ^ (prefixWord ++ tailWord_2528930).sum := by decide
  have hdescent : baseEnd_2528930 < baseStart_2528930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528946 : List Nat := [3, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2]
def baseStart_2528946 : Nat := 118140960795 + 2528946 * 2 ^ 59
def prefixEnd_2528946 : Nat := 4983230072969 + 3 ^ 40 * 2528946 * 2
def baseEnd_2528946 : Nat := 1298564847265367720844595

theorem tailTrace_2528946 : CollatzResearch.WordTrace tailWord_2528946 prefixEnd_2528946 1298564847265367720844595 := by
  unfold tailWord_2528946
  simp only [CollatzResearch.WordTrace]
  refine ⟨23059559574017006608957673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61492158864045350957220461 23059559574017006608957673)
  ·
    refine ⟨17294669680512754956718255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23059559574017006608957673 17294669680512754956718255)
    ·
      refine ⟨25942004520769132435077383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17294669680512754956718255 25942004520769132435077383)
      ·
        refine ⟨38913006781153698652616075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25942004520769132435077383 38913006781153698652616075)
        ·
          refine ⟨58369510171730547978924113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38913006781153698652616075 58369510171730547978924113)
          ·
            refine ⟨43777132628797910984193085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58369510171730547978924113 43777132628797910984193085)
            ·
              refine ⟨16416424735799216619072407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43777132628797910984193085 16416424735799216619072407)
              ·
                refine ⟨24624637103698824928608611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16416424735799216619072407 24624637103698824928608611)
                ·
                  refine ⟨36936955655548237392912917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24624637103698824928608611 36936955655548237392912917)
                  ·
                    refine ⟨1731419796353823627792793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 36936955655548237392912917 1731419796353823627792793)
                    ·
                      refine ⟨1298564847265367720844595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1731419796353823627792793 1298564847265367720844595)
                      ·
                        rfl

theorem cell23_2528946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2].length) (baseStart_2528946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2528946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2528946 prefixEnd_2528946 := by exact prefixLift 2528946
  have htrace : WordTrace (prefixWord ++ tailWord_2528946) baseStart_2528946 baseEnd_2528946 := by
    simpa [prefixWord, tailWord_2528946, baseEnd_2528946] using wordTrace_append hprefix tailTrace_2528946
  have hstable : (prefixWord ++ tailWord_2528946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528946).length < 2 ^ (prefixWord ++ tailWord_2528946).sum := by decide
  have hdescent : baseEnd_2528946 < baseStart_2528946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528956 : List Nat := [2, 2, 2, 3, 1, 2, 1, 1, 5, 4]
def baseStart_2528956 : Nat := 118140960795 + 2528956 * 2 ^ 59
def prefixEnd_2528956 : Nat := 4983230072969 + 3 ^ 40 * 2528956 * 2
def baseEnd_2528956 : Nat := 432856660690637560573183

theorem tailTrace_2528956 : CollatzResearch.WordTrace tailWord_2528956 prefixEnd_2528956 432856660690637560573183 := by
  unfold tailWord_2528956
  simp only [CollatzResearch.WordTrace]
  refine ⟨46119301513015899071847361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61492402017354532095796481 46119301513015899071847361)
  ·
    refine ⟨34589476134761924303885521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46119301513015899071847361 34589476134761924303885521)
    ·
      refine ⟨25942107101071443227914141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34589476134761924303885521 25942107101071443227914141)
      ·
        refine ⟨9728290162901791210467803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25942107101071443227914141 9728290162901791210467803)
        ·
          refine ⟨14592435244352686815701705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9728290162901791210467803 14592435244352686815701705)
          ·
            refine ⟨10944326433264515111776279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14592435244352686815701705 10944326433264515111776279)
            ·
              refine ⟨16416489649896772667664419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10944326433264515111776279 16416489649896772667664419)
              ·
                refine ⟨24624734474845159001496629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16416489649896772667664419 24624734474845159001496629)
                ·
                  refine ⟨2308568857016733656390309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24624734474845159001496629 2308568857016733656390309)
                  ·
                    refine ⟨432856660690637560573183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2308568857016733656390309 432856660690637560573183)
                    ·
                      rfl

theorem cell23_2528956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 5, 4].length) (baseStart_2528956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2528956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2528956 prefixEnd_2528956 := by exact prefixLift 2528956
  have htrace : WordTrace (prefixWord ++ tailWord_2528956) baseStart_2528956 baseEnd_2528956 := by
    simpa [prefixWord, tailWord_2528956, baseEnd_2528956] using wordTrace_append hprefix tailTrace_2528956
  have hstable : (prefixWord ++ tailWord_2528956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528956).length < 2 ^ (prefixWord ++ tailWord_2528956).sum := by decide
  have hdescent : baseEnd_2528956 < baseStart_2528956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528986 : List Nat := [3, 1, 1, 2, 2, 3, 3, 2, 6]
def baseStart_2528986 : Nat := 118140960795 + 2528986 * 2 ^ 59
def prefixEnd_2528986 : Nat := 4983230072969 + 3 ^ 40 * 2528986 * 2
def baseEnd_2528986 : Nat := 144287265165727507149379

theorem tailTrace_2528986 : CollatzResearch.WordTrace tailWord_2528986 prefixEnd_2528986 144287265165727507149379 := by
  unfold tailWord_2528986
  simp only [CollatzResearch.WordTrace]
  refine ⟨23059924303980778316821703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61493131477282075511524541 23059924303980778316821703)
  ·
    refine ⟨34589886455971167475232555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23059924303980778316821703 34589886455971167475232555)
    ·
      refine ⟨51884829683956751212848833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34589886455971167475232555 51884829683956751212848833)
      ·
        refine ⟨38913622262967563409636625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51884829683956751212848833 38913622262967563409636625)
        ·
          refine ⟨29185216697225672557227469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38913622262967563409636625 29185216697225672557227469)
          ·
            refine ⟨10944456261459627208960301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29185216697225672557227469 10944456261459627208960301)
            ·
              refine ⟨4104171098047360203360113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10944456261459627208960301 4104171098047360203360113)
              ·
                refine ⟨3078128323535520152520085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4104171098047360203360113 3078128323535520152520085)
                ·
                  refine ⟨144287265165727507149379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3078128323535520152520085 144287265165727507149379)
                  ·
                    rfl

theorem cell23_2528986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 2, 6].length) (baseStart_2528986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2528986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2528986 prefixEnd_2528986 := by exact prefixLift 2528986
  have htrace : WordTrace (prefixWord ++ tailWord_2528986) baseStart_2528986 baseEnd_2528986 := by
    simpa [prefixWord, tailWord_2528986, baseEnd_2528986] using wordTrace_append hprefix tailTrace_2528986
  have hstable : (prefixWord ++ tailWord_2528986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528986).length < 2 ^ (prefixWord ++ tailWord_2528986).sum := by decide
  have hdescent : baseEnd_2528986 < baseStart_2528986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529054 : List Nat := [4, 3, 2, 2, 1, 2, 2, 1, 6]
def baseStart_2529054 : Nat := 118140960795 + 2529054 * 2 ^ 59
def prefixEnd_2529054 : Nat := 4983230072969 + 3 ^ 40 * 2529054 * 2
def baseEnd_2529054 : Nat := 144291144797339255366011

theorem tailTrace_2529054 : CollatzResearch.WordTrace tailWord_2529054 prefixEnd_2529054 144291144797339255366011 := by
  unfold tailWord_2529054
  simp only [CollatzResearch.WordTrace]
  refine ⟨11530272172459595110095277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61494784919784507253841477 11530272172459595110095277)
  ·
    refine ⟨4323852064672348166285729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11530272172459595110095277 4323852064672348166285729)
    ·
      refine ⟨3242889048504261124714297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4323852064672348166285729 3242889048504261124714297)
      ·
        refine ⟨2432166786378195843535723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3242889048504261124714297 2432166786378195843535723)
        ·
          refine ⟨3648250179567293765303585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2432166786378195843535723 3648250179567293765303585)
          ·
            refine ⟨2736187634675470323977689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3648250179567293765303585 2736187634675470323977689)
            ·
              refine ⟨2052140726006602742983267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2736187634675470323977689 2052140726006602742983267)
              ·
                refine ⟨3078211089009904114474901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2052140726006602742983267 3078211089009904114474901)
                ·
                  refine ⟨144291144797339255366011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3078211089009904114474901 144291144797339255366011)
                  ·
                    rfl

theorem cell23_2529054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_2529054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2529054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2529054 prefixEnd_2529054 := by exact prefixLift 2529054
  have htrace : WordTrace (prefixWord ++ tailWord_2529054) baseStart_2529054 baseEnd_2529054 := by
    simpa [prefixWord, tailWord_2529054, baseEnd_2529054] using wordTrace_append hprefix tailTrace_2529054
  have hstable : (prefixWord ++ tailWord_2529054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529054).length < 2 ^ (prefixWord ++ tailWord_2529054).sum := by decide
  have hdescent : baseEnd_2529054 < baseStart_2529054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529056 : List Nat := [2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 5]
def baseStart_2529056 : Nat := 118140960795 + 2529056 * 2 ^ 59
def prefixEnd_2529056 : Nat := 4983230072969 + 3 ^ 40 * 2529056 * 2
def baseEnd_2529056 : Nat := 1298621330137362290469089

theorem tailTrace_2529056 : CollatzResearch.WordTrace tailWord_2529056 prefixEnd_2529056 1298621330137362290469089 := by
  unfold tailWord_2529056
  simp only [CollatzResearch.WordTrace]
  refine ⟨46121125162834757611167511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61494833550446343481556681 46121125162834757611167511)
  ·
    refine ⟨69181687744252136416751267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46121125162834757611167511 69181687744252136416751267)
    ·
      refine ⟨103772531616378204625126901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69181687744252136416751267 103772531616378204625126901)
      ·
        refine ⟨9728674839035456683605647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 103772531616378204625126901 9728674839035456683605647)
        ·
          refine ⟨14593012258553185025408471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9728674839035456683605647 14593012258553185025408471)
          ·
            refine ⟨21889518387829777538112707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14593012258553185025408471 21889518387829777538112707)
            ·
              refine ⟨32834277581744666307169061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21889518387829777538112707 32834277581744666307169061)
              ·
                refine ⟨6156427046577124932594199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32834277581744666307169061 6156427046577124932594199)
                ·
                  refine ⟨9234640569865687398891299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6156427046577124932594199 9234640569865687398891299)
                  ·
                    refine ⟨13851960854798531098336949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9234640569865687398891299 13851960854798531098336949)
                    ·
                      refine ⟨1298621330137362290469089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13851960854798531098336949 1298621330137362290469089)
                      ·
                        rfl

theorem cell23_2529056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_2529056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2529056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2529056 prefixEnd_2529056 := by exact prefixLift 2529056
  have htrace : WordTrace (prefixWord ++ tailWord_2529056) baseStart_2529056 baseEnd_2529056 := by
    simpa [prefixWord, tailWord_2529056, baseEnd_2529056] using wordTrace_append hprefix tailTrace_2529056
  have hstable : (prefixWord ++ tailWord_2529056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529056).length < 2 ^ (prefixWord ++ tailWord_2529056).sum := by decide
  have hdescent : baseEnd_2529056 < baseStart_2529056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529059 : List Nat := [1, 1, 1, 4, 2, 1, 3, 10]
def baseStart_2529059 : Nat := 118140960795 + 2529059 * 2 ^ 59
def prefixEnd_2529059 : Nat := 4983230072969 + 3 ^ 40 * 2529059 * 2
def baseEnd_2529059 : Nat := 48097143354789843656725

theorem tailTrace_2529059 : CollatzResearch.WordTrace tailWord_2529059 prefixEnd_2529059 48097143354789843656725 := by
  unfold tailWord_2529059
  simp only [CollatzResearch.WordTrace]
  refine ⟨92242359744658646734694231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61494906496439097823129487 92242359744658646734694231)
  ·
    refine ⟨138363539616987970102041347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92242359744658646734694231 138363539616987970102041347)
    ·
      refine ⟨207545309425481955153062021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138363539616987970102041347 207545309425481955153062021)
      ·
        refine ⟨38914745517277866591199129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 207545309425481955153062021 38914745517277866591199129)
        ·
          refine ⟨29186059137958399943399347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38914745517277866591199129 29186059137958399943399347)
          ·
            refine ⟨43779088706937599915099021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29186059137958399943399347 43779088706937599915099021)
            ·
              refine ⟨16417158265101599968162133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43779088706937599915099021 16417158265101599968162133)
              ·
                refine ⟨48097143354789843656725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 16417158265101599968162133 48097143354789843656725)
                ·
                  rfl

theorem cell23_2529059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 10].length) (baseStart_2529059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2529059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2529059 prefixEnd_2529059 := by exact prefixLift 2529059
  have htrace : WordTrace (prefixWord ++ tailWord_2529059) baseStart_2529059 baseEnd_2529059 := by
    simpa [prefixWord, tailWord_2529059, baseEnd_2529059] using wordTrace_append hprefix tailTrace_2529059
  have hstable : (prefixWord ++ tailWord_2529059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529059).length < 2 ^ (prefixWord ++ tailWord_2529059).sum := by decide
  have hdescent : baseEnd_2529059 < baseStart_2529059 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529070 : List Nat := [4, 1, 3, 2, 2, 1, 1, 1, 3, 1, 4]
def baseStart_2529070 : Nat := 118140960795 + 2529070 * 2 ^ 59
def prefixEnd_2529070 : Nat := 4983230072969 + 3 ^ 40 * 2529070 * 2
def baseEnd_2529070 : Nat := 1298628518866525235694025

theorem tailTrace_2529070 : CollatzResearch.WordTrace tailWord_2529070 prefixEnd_2529070 1298628518866525235694025 := by
  unfold tailWord_2529070
  simp only [CollatzResearch.WordTrace]
  refine ⟨11530345118452349451668083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61495173965079197075563109 11530345118452349451668083)
  ·
    refine ⟨17295517677678524177502125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11530345118452349451668083 17295517677678524177502125)
    ·
      refine ⟨6485819129129446566563297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17295517677678524177502125 6485819129129446566563297)
      ·
        refine ⟨4864364346847084924922473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6485819129129446566563297 4864364346847084924922473)
        ·
          refine ⟨3648273260135313693691855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4864364346847084924922473 3648273260135313693691855)
          ·
            refine ⟨5472409890202970540537783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3648273260135313693691855 5472409890202970540537783)
            ·
              refine ⟨8208614835304455810806675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5472409890202970540537783 8208614835304455810806675)
              ·
                refine ⟨12312922252956683716210013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8208614835304455810806675 12312922252956683716210013)
                ·
                  refine ⟨4617345844858756393578755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12312922252956683716210013 4617345844858756393578755)
                  ·
                    refine ⟨6926018767288134590368133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4617345844858756393578755 6926018767288134590368133)
                    ·
                      refine ⟨1298628518866525235694025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6926018767288134590368133 1298628518866525235694025)
                      ·
                        rfl

theorem cell23_2529070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_2529070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2529070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2529070 prefixEnd_2529070 := by exact prefixLift 2529070
  have htrace : WordTrace (prefixWord ++ tailWord_2529070) baseStart_2529070 baseEnd_2529070 := by
    simpa [prefixWord, tailWord_2529070, baseEnd_2529070] using wordTrace_append hprefix tailTrace_2529070
  have hstable : (prefixWord ++ tailWord_2529070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529070).length < 2 ^ (prefixWord ++ tailWord_2529070).sum := by decide
  have hdescent : baseEnd_2529070 < baseStart_2529070 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529073 : List Nat := [1, 2, 2, 3, 2, 3, 1, 1, 3, 2, 3]
def baseStart_2529073 : Nat := 118140960795 + 2529073 * 2 ^ 59
def prefixEnd_2529073 : Nat := 4983230072969 + 3 ^ 40 * 2529073 * 2
def baseEnd_2529073 : Nat := 1298630059308488723956511

theorem tailTrace_2529073 : CollatzResearch.WordTrace tailWord_2529073 prefixEnd_2529073 1298630059308488723956511 := by
  unfold tailWord_2529073
  simp only [CollatzResearch.WordTrace]
  refine ⟨92242870366607927125703873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61495246911071951417135915 92242870366607927125703873)
  ·
    refine ⟨69182152774955945344277905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92242870366607927125703873 69182152774955945344277905)
    ·
      refine ⟨51886614581216959008208429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69182152774955945344277905 51886614581216959008208429)
      ·
        refine ⟨19457480467956359628078161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51886614581216959008208429 19457480467956359628078161)
        ·
          refine ⟨14593110350967269721058621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19457480467956359628078161 14593110350967269721058621)
          ·
            refine ⟨5472416381612726145396983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14593110350967269721058621 5472416381612726145396983)
            ·
              refine ⟨8208624572419089218095475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5472416381612726145396983 8208624572419089218095475)
              ·
                refine ⟨12312936858628633827143213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8208624572419089218095475 12312936858628633827143213)
                ·
                  refine ⟨4617351321985737685178705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12312936858628633827143213 4617351321985737685178705)
                  ·
                    refine ⟨3463013491489303263884029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4617351321985737685178705 3463013491489303263884029)
                    ·
                      refine ⟨1298630059308488723956511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3463013491489303263884029 1298630059308488723956511)
                      ·
                        rfl

theorem cell23_2529073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_2529073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2529073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2529073 prefixEnd_2529073 := by exact prefixLift 2529073
  have htrace : WordTrace (prefixWord ++ tailWord_2529073) baseStart_2529073 baseEnd_2529073 := by
    simpa [prefixWord, tailWord_2529073, baseEnd_2529073] using wordTrace_append hprefix tailTrace_2529073
  have hstable : (prefixWord ++ tailWord_2529073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529073).length < 2 ^ (prefixWord ++ tailWord_2529073).sum := by decide
  have hdescent : baseEnd_2529073 < baseStart_2529073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529099 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 7]
def baseStart_2529099 : Nat := 118140960795 + 2529099 * 2 ^ 59
def prefixEnd_2529099 : Nat := 4983230072969 + 3 ^ 40 * 2529099 * 2
def baseEnd_2529099 : Nat := 1298643409805505622231391

theorem tailTrace_2529099 : CollatzResearch.WordTrace tailWord_2529099 prefixEnd_2529099 1298643409805505622231391 := by
  unfold tailWord_2529099
  simp only [CollatzResearch.WordTrace]
  refine ⟨92243818664513733566150351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61495879109675822377433567 92243818664513733566150351)
  ·
    refine ⟨138365727996770600349225527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92243818664513733566150351 138365727996770600349225527)
    ·
      refine ⟨207548591995155900523838291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138365727996770600349225527 207548591995155900523838291)
      ·
        refine ⟨311322887992733850785757437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207548591995155900523838291 311322887992733850785757437)
        ·
          refine ⟨116746082997275194044659039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 311322887992733850785757437 116746082997275194044659039)
          ·
            refine ⟨175119124495912791066988559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116746082997275194044659039 175119124495912791066988559)
            ·
              refine ⟨262678686743869186600482839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175119124495912791066988559 262678686743869186600482839)
              ·
                refine ⟨394018030115803779900724259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 262678686743869186600482839 394018030115803779900724259)
                ·
                  refine ⟨591027045173705669851086389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 394018030115803779900724259 591027045173705669851086389)
                  ·
                    refine ⟨55408785485034906548539349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 591027045173705669851086389 55408785485034906548539349)
                    ·
                      refine ⟨1298643409805505622231391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 55408785485034906548539349 1298643409805505622231391)
                      ·
                        rfl

theorem cell23_2529099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 7].length) (baseStart_2529099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2529099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2529099 prefixEnd_2529099 := by exact prefixLift 2529099
  have htrace : WordTrace (prefixWord ++ tailWord_2529099) baseStart_2529099 baseEnd_2529099 := by
    simpa [prefixWord, tailWord_2529099, baseEnd_2529099] using wordTrace_append hprefix tailTrace_2529099
  have hstable : (prefixWord ++ tailWord_2529099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529099).length < 2 ^ (prefixWord ++ tailWord_2529099).sum := by decide
  have hdescent : baseEnd_2529099 < baseStart_2529099 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529106 : List Nat := [3, 2, 2, 1, 1, 3, 1, 1, 2, 7]
def baseStart_2529106 : Nat := 118140960795 + 2529106 * 2 ^ 59
def prefixEnd_2529106 : Nat := 4983230072969 + 3 ^ 40 * 2529106 * 2
def baseEnd_2529106 : Nat := 432882334723362364947953

theorem tailTrace_2529106 : CollatzResearch.WordTrace tailWord_2529106 prefixEnd_2529106 432882334723362364947953 := by
  unfold tailWord_2529106
  simp only [CollatzResearch.WordTrace]
  refine ⟨23061018493872093440413793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61496049316992249174436781 23061018493872093440413793)
  ·
    refine ⟨17295763870404070080310345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23061018493872093440413793 17295763870404070080310345)
    ·
      refine ⟨12971822902803052560232759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17295763870404070080310345 12971822902803052560232759)
      ·
        refine ⟨19457734354204578840349139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12971822902803052560232759 19457734354204578840349139)
        ·
          refine ⟨29186601531306868260523709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19457734354204578840349139 29186601531306868260523709)
          ·
            refine ⟨10944975574240075597696391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29186601531306868260523709 10944975574240075597696391)
            ·
              refine ⟨16417463361360113396544587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10944975574240075597696391 16417463361360113396544587)
              ·
                refine ⟨24626195042040170094816881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16417463361360113396544587 24626195042040170094816881)
                ·
                  refine ⟨18469646281530127571112661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24626195042040170094816881 18469646281530127571112661)
                  ·
                    refine ⟨432882334723362364947953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18469646281530127571112661 432882334723362364947953)
                    ·
                      rfl

theorem cell23_2529106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_2529106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2529106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2529106 prefixEnd_2529106 := by exact prefixLift 2529106
  have htrace : WordTrace (prefixWord ++ tailWord_2529106) baseStart_2529106 baseEnd_2529106 := by
    simpa [prefixWord, tailWord_2529106, baseEnd_2529106] using wordTrace_append hprefix tailTrace_2529106
  have hstable : (prefixWord ++ tailWord_2529106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529106).length < 2 ^ (prefixWord ++ tailWord_2529106).sum := by decide
  have hdescent : baseEnd_2529106 < baseStart_2529106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529113 : List Nat := [1, 2, 1, 2, 2, 3, 1, 1, 5, 3, 2]
def baseStart_2529113 : Nat := 118140960795 + 2529113 * 2 ^ 59
def prefixEnd_2529113 : Nat := 4983230072969 + 3 ^ 40 * 2529113 * 2
def baseEnd_2529113 : Nat := 1298650598534668567456327

theorem tailTrace_2529113 : CollatzResearch.WordTrace tailWord_2529113 prefixEnd_2529113 1298650598534668567456327 := by
  unfold tailWord_2529113
  simp only [CollatzResearch.WordTrace]
  refine ⟨92244329286463013957159993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61496219524308675971439995 92244329286463013957159993)
  ·
    refine ⟨69183246964847260467869995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92244329286463013957159993 69183246964847260467869995)
    ·
      refine ⟨103774870447270890701804993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69183246964847260467869995 103774870447270890701804993)
      ·
        refine ⟨77831152835453168026353745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103774870447270890701804993 77831152835453168026353745)
        ·
          refine ⟨58373364626589876019765309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77831152835453168026353745 58373364626589876019765309)
          ·
            refine ⟨21890011734971203507411991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58373364626589876019765309 21890011734971203507411991)
            ·
              refine ⟨32835017602456805261117987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21890011734971203507411991 32835017602456805261117987)
              ·
                refine ⟨49252526403685207891676981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32835017602456805261117987 49252526403685207891676981)
                ·
                  refine ⟨4617424350345488239844717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49252526403685207891676981 4617424350345488239844717)
                  ·
                    refine ⟨1731534131379558089941769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4617424350345488239844717 1731534131379558089941769)
                    ·
                      refine ⟨1298650598534668567456327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1731534131379558089941769 1298650598534668567456327)
                      ·
                        rfl

theorem cell23_2529113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 5, 3, 2].length) (baseStart_2529113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2529113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2529113 prefixEnd_2529113 := by exact prefixLift 2529113
  have htrace : WordTrace (prefixWord ++ tailWord_2529113) baseStart_2529113 baseEnd_2529113 := by
    simpa [prefixWord, tailWord_2529113, baseEnd_2529113] using wordTrace_append hprefix tailTrace_2529113
  have hstable : (prefixWord ++ tailWord_2529113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529113).length < 2 ^ (prefixWord ++ tailWord_2529113).sum := by decide
  have hdescent : baseEnd_2529113 < baseStart_2529113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529120 : List Nat := [2, 1, 1, 3, 3, 2, 2, 3, 2, 1, 3]
def baseStart_2529120 : Nat := 118140960795 + 2529120 * 2 ^ 59
def prefixEnd_2529120 : Nat := 4983230072969 + 3 ^ 40 * 2529120 * 2
def baseEnd_2529120 : Nat := 1298654192899250040068795

theorem tailTrace_2529120 : CollatzResearch.WordTrace tailWord_2529120 prefixEnd_2529120 1298654192899250040068795 := by
  unfold tailWord_2529120
  simp only [CollatzResearch.WordTrace]
  refine ⟨46122292298718827076332407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61496389731625102768443209 46122292298718827076332407)
  ·
    refine ⟨69183438448078240614498611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46122292298718827076332407 69183438448078240614498611)
    ·
      refine ⟨103775157672117360921747917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69183438448078240614498611 103775157672117360921747917)
      ·
        refine ⟨38915684127044010345655469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103775157672117360921747917 38915684127044010345655469)
        ·
          refine ⟨14593381547641503879620801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38915684127044010345655469 14593381547641503879620801)
          ·
            refine ⟨10945036160731127909715601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14593381547641503879620801 10945036160731127909715601)
            ·
              refine ⟨8208777120548345932286701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10945036160731127909715601 8208777120548345932286701)
              ·
                refine ⟨3078291420205629724607513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8208777120548345932286701 3078291420205629724607513)
                ·
                  refine ⟨2308718565154222293455635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3078291420205629724607513 2308718565154222293455635)
                  ·
                    refine ⟨3463077847731333440183453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2308718565154222293455635 3463077847731333440183453)
                    ·
                      refine ⟨1298654192899250040068795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3463077847731333440183453 1298654192899250040068795)
                      ·
                        rfl

theorem cell23_2529120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 3, 2, 1, 3].length) (baseStart_2529120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2529120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2529120 prefixEnd_2529120 := by exact prefixLift 2529120
  have htrace : WordTrace (prefixWord ++ tailWord_2529120) baseStart_2529120 baseEnd_2529120 := by
    simpa [prefixWord, tailWord_2529120, baseEnd_2529120] using wordTrace_append hprefix tailTrace_2529120
  have hstable : (prefixWord ++ tailWord_2529120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529120).length < 2 ^ (prefixWord ++ tailWord_2529120).sum := by decide
  have hdescent : baseEnd_2529120 < baseStart_2529120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529146 : List Nat := [3, 1, 1, 1, 1, 1, 4, 3, 2, 1, 5]
def baseStart_2529146 : Nat := 118140960795 + 2529146 * 2 ^ 59
def prefixEnd_2529146 : Nat := 4983230072969 + 3 ^ 40 * 2529146 * 2
def baseEnd_2529146 : Nat := 1298667543396266938343675

theorem tailTrace_2529146 : CollatzResearch.WordTrace tailWord_2529146 prefixEnd_2529146 1298667543396266938343675 := by
  unfold tailWord_2529146
  simp only [CollatzResearch.WordTrace]
  refine ⟨23061383223835865148277823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61497021930228973728740861 23061383223835865148277823)
  ·
    refine ⟨34592074835753797722416735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23061383223835865148277823 34592074835753797722416735)
    ·
      refine ⟨51888112253630696583625103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34592074835753797722416735 51888112253630696583625103)
      ·
        refine ⟨77832168380446044875437655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51888112253630696583625103 77832168380446044875437655)
        ·
          refine ⟨116748252570669067313156483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77832168380446044875437655 116748252570669067313156483)
          ·
            refine ⟨175122378856003600969734725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116748252570669067313156483 175122378856003600969734725)
            ·
              refine ⟨32835446035500675181825261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 175122378856003600969734725 32835446035500675181825261)
              ·
                refine ⟨12313292263312753193184473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32835446035500675181825261 12313292263312753193184473)
                ·
                  refine ⟨9234969197484564894888355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12313292263312753193184473 9234969197484564894888355)
                  ·
                    refine ⟨13852453796226847342332533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9234969197484564894888355 13852453796226847342332533)
                    ·
                      refine ⟨1298667543396266938343675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13852453796226847342332533 1298667543396266938343675)
                      ·
                        rfl

theorem cell23_2529146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 2, 1, 5].length) (baseStart_2529146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2529146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2529146 prefixEnd_2529146 := by exact prefixLift 2529146
  have htrace : WordTrace (prefixWord ++ tailWord_2529146) baseStart_2529146 baseEnd_2529146 := by
    simpa [prefixWord, tailWord_2529146, baseEnd_2529146] using wordTrace_append hprefix tailTrace_2529146
  have hstable : (prefixWord ++ tailWord_2529146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529146).length < 2 ^ (prefixWord ++ tailWord_2529146).sum := by decide
  have hdescent : baseEnd_2529146 < baseStart_2529146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529213 : List Nat := [1, 4, 1, 2, 3, 1, 1, 1, 4, 5]
def baseStart_2529213 : Nat := 118140960795 + 2529213 * 2 ^ 59
def prefixEnd_2529213 : Nat := 4983230072969 + 3 ^ 40 * 2529213 * 2
def baseEnd_2529213 : Nat := 432900648866706058735289

theorem tailTrace_2529213 : CollatzResearch.WordTrace tailWord_2529213 prefixEnd_2529213 432900648866706058735289 := by
  unfold tailWord_2529213
  simp only [CollatzResearch.WordTrace]
  refine ⟨92247976586100731035800293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61498651057400487357200195 92247976586100731035800293)
  ·
    refine ⟨17296495609893887069212555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92247976586100731035800293 17296495609893887069212555)
    ·
      refine ⟨25944743414840830603818833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17296495609893887069212555 25944743414840830603818833)
      ·
        refine ⟨19458557561130622952864125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25944743414840830603818833 19458557561130622952864125)
        ·
          refine ⟨7296959085423983607324047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19458557561130622952864125 7296959085423983607324047)
          ·
            refine ⟨10945438628135975410986071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7296959085423983607324047 10945438628135975410986071)
            ·
              refine ⟨16418157942203963116479107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10945438628135975410986071 16418157942203963116479107)
              ·
                refine ⟨24627236913305944674718661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16418157942203963116479107 24627236913305944674718661)
                ·
                  refine ⟨4617606921244864626509749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24627236913305944674718661 4617606921244864626509749)
                  ·
                    refine ⟨432900648866706058735289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4617606921244864626509749 432900648866706058735289)
                    ·
                      rfl

theorem cell23_2529213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 4, 5].length) (baseStart_2529213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2529213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2529213 prefixEnd_2529213 := by exact prefixLift 2529213
  have htrace : WordTrace (prefixWord ++ tailWord_2529213) baseStart_2529213 baseEnd_2529213 := by
    simpa [prefixWord, tailWord_2529213, baseEnd_2529213] using wordTrace_append hprefix tailTrace_2529213
  have hstable : (prefixWord ++ tailWord_2529213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529213).length < 2 ^ (prefixWord ++ tailWord_2529213).sum := by decide
  have hdescent : baseEnd_2529213 < baseStart_2529213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529273 : List Nat := [1, 2, 1, 3, 1, 4, 1, 4, 6]
def baseStart_2529273 : Nat := 118140960795 + 2529273 * 2 ^ 59
def prefixEnd_2529273 : Nat := 4983230072969 + 3 ^ 40 * 2529273 * 2
def baseEnd_2529273 : Nat := 144303639493265326828399

theorem tailTrace_2529273 : CollatzResearch.WordTrace tailWord_2529273 prefixEnd_2529273 144303639493265326828399 := by
  unfold tailWord_2529273
  simp only [CollatzResearch.WordTrace]
  refine ⟨92250164965883361282984473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61500109977255574188656315 92250164965883361282984473)
  ·
    refine ⟨69187623724412520962238355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92250164965883361282984473 69187623724412520962238355)
    ·
      refine ⟨103781435586618781443357533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69187623724412520962238355 103781435586618781443357533)
      ·
        refine ⟨38918038344982043041259075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103781435586618781443357533 38918038344982043041259075)
        ·
          refine ⟨58377057517473064561888613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38918038344982043041259075 58377057517473064561888613)
          ·
            refine ⟨10945698284526199605354115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58377057517473064561888613 10945698284526199605354115)
            ·
              refine ⟨16418547426789299408031173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10945698284526199605354115 16418547426789299408031173)
              ·
                refine ⟨3078477642522993639005845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16418547426789299408031173 3078477642522993639005845)
                ·
                  refine ⟨144303639493265326828399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3078477642522993639005845 144303639493265326828399)
                  ·
                    rfl

theorem cell23_2529273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 4, 6].length) (baseStart_2529273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2529273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2529273 prefixEnd_2529273 := by exact prefixLift 2529273
  have htrace : WordTrace (prefixWord ++ tailWord_2529273) baseStart_2529273 baseEnd_2529273 := by
    simpa [prefixWord, tailWord_2529273, baseEnd_2529273] using wordTrace_append hprefix tailTrace_2529273
  have hstable : (prefixWord ++ tailWord_2529273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529273).length < 2 ^ (prefixWord ++ tailWord_2529273).sum := by decide
  have hdescent : baseEnd_2529273 < baseStart_2529273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529284 : List Nat := [2, 3, 2, 4, 1, 1, 1, 1, 2, 4, 2]
def baseStart_2529284 : Nat := 118140960795 + 2529284 * 2 ^ 59
def prefixEnd_2529284 : Nat := 4983230072969 + 3 ^ 40 * 2529284 * 2
def baseEnd_2529284 : Nat := 1298738403726587398418041

theorem tailTrace_2529284 : CollatzResearch.WordTrace tailWord_2529284 prefixEnd_2529284 1298738403726587398418041 := by
  unfold tailWord_2529284
  simp only [CollatzResearch.WordTrace]
  refine ⟨46125283084421755080817453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61500377445895673441089937 46125283084421755080817453)
  ·
    refine ⟨17296981156658158155306545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46125283084421755080817453 17296981156658158155306545)
    ·
      refine ⟨12972735867493618616479909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17296981156658158155306545 12972735867493618616479909)
      ·
        refine ⟨2432387975155053490589983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12972735867493618616479909 2432387975155053490589983)
        ·
          refine ⟨3648581962732580235884975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2432387975155053490589983 3648581962732580235884975)
          ·
            refine ⟨5472872944098870353827463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3648581962732580235884975 5472872944098870353827463)
            ·
              refine ⟨8209309416148305530741195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5472872944098870353827463 8209309416148305530741195)
              ·
                refine ⟨12313964124222458296111793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8209309416148305530741195 12313964124222458296111793)
                ·
                  refine ⟨9235473093166843722083845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12313964124222458296111793 9235473093166843722083845)
                  ·
                    refine ⟨1731651204968783197890721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9235473093166843722083845 1731651204968783197890721)
                    ·
                      refine ⟨1298738403726587398418041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1731651204968783197890721 1298738403726587398418041)
                      ·
                        rfl

theorem cell23_2529284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_2529284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2529284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2529284 prefixEnd_2529284 := by exact prefixLift 2529284
  have htrace : WordTrace (prefixWord ++ tailWord_2529284) baseStart_2529284 baseEnd_2529284 := by
    simpa [prefixWord, tailWord_2529284, baseEnd_2529284] using wordTrace_append hprefix tailTrace_2529284
  have hstable : (prefixWord ++ tailWord_2529284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529284).length < 2 ^ (prefixWord ++ tailWord_2529284).sum := by decide
  have hdescent : baseEnd_2529284 < baseStart_2529284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529323 : List Nat := [1, 1, 1, 1, 2, 1, 4, 2, 5, 1, 4]
def baseStart_2529323 : Nat := 118140960795 + 2529323 * 2 ^ 59
def prefixEnd_2529323 : Nat := 4983230072969 + 3 ^ 40 * 2529323 * 2
def baseEnd_2529323 : Nat := 1298758429472112745830361

theorem tailTrace_2529323 : CollatzResearch.WordTrace tailWord_2529323 prefixEnd_2529323 1298758429472112745830361 := by
  unfold tailWord_2529323
  simp only [CollatzResearch.WordTrace]
  refine ⟨92251988615702219822304623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61501325743801479881536415 92251988615702219822304623)
  ·
    refine ⟨138377982923553329733456935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92251988615702219822304623 138377982923553329733456935)
    ·
      refine ⟨207566974385329994600185403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138377982923553329733456935 207566974385329994600185403)
      ·
        refine ⟨311350461577994991900278105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207566974385329994600185403 311350461577994991900278105)
        ·
          refine ⟨233512846183496243925208579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 311350461577994991900278105 233512846183496243925208579)
          ·
            refine ⟨350269269275244365887812869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233512846183496243925208579 350269269275244365887812869)
            ·
              refine ⟨65675487989108318603964913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 350269269275244365887812869 65675487989108318603964913)
              ·
                refine ⟨49256615991831238952973685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65675487989108318603964913 49256615991831238952973685)
                ·
                  refine ⟨4617807749234178651841283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49256615991831238952973685 4617807749234178651841283)
                  ·
                    refine ⟨6926711623851267977761925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4617807749234178651841283 6926711623851267977761925)
                    ·
                      refine ⟨1298758429472112745830361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6926711623851267977761925 1298758429472112745830361)
                      ·
                        rfl

theorem cell23_2529323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 5, 1, 4].length) (baseStart_2529323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2529323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2529323 prefixEnd_2529323 := by exact prefixLift 2529323
  have htrace : WordTrace (prefixWord ++ tailWord_2529323) baseStart_2529323 baseEnd_2529323 := by
    simpa [prefixWord, tailWord_2529323, baseEnd_2529323] using wordTrace_append hprefix tailTrace_2529323
  have hstable : (prefixWord ++ tailWord_2529323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529323).length < 2 ^ (prefixWord ++ tailWord_2529323).sum := by decide
  have hdescent : baseEnd_2529323 < baseStart_2529323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529333 : List Nat := [1, 3, 3, 1, 1, 1, 2, 2, 3, 6]
def baseStart_2529333 : Nat := 118140960795 + 2529333 * 2 ^ 59
def prefixEnd_2529333 : Nat := 4983230072969 + 3 ^ 40 * 2529333 * 2
def baseEnd_2529333 : Nat := 432921188092885902235105

theorem tailTrace_2529333 : CollatzResearch.WordTrace tailWord_2529333 prefixEnd_2529333 432921188092885902235105 := by
  unfold tailWord_2529333
  simp only [CollatzResearch.WordTrace]
  refine ⟨92252353345665991530168653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61501568897110661020112435 92252353345665991530168653)
  ·
    refine ⟨34594632504624746823813245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92252353345665991530168653 34594632504624746823813245)
    ·
      refine ⟨12972987189234280058929967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34594632504624746823813245 12972987189234280058929967)
      ·
        refine ⟨19459480783851420088394951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12972987189234280058929967 19459480783851420088394951)
        ·
          refine ⟨29189221175777130132592427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19459480783851420088394951 29189221175777130132592427)
          ·
            refine ⟨43783831763665695198888641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29189221175777130132592427 43783831763665695198888641)
            ·
              refine ⟨32837873822749271399166481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43783831763665695198888641 32837873822749271399166481)
              ·
                refine ⟨24628405367061953549374861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32837873822749271399166481 24628405367061953549374861)
                ·
                  refine ⟨9235652012648232581015573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24628405367061953549374861 9235652012648232581015573)
                  ·
                    refine ⟨432921188092885902235105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9235652012648232581015573 432921188092885902235105)
                    ·
                      rfl

theorem cell23_2529333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_2529333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2529333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2529333 prefixEnd_2529333 := by exact prefixLift 2529333
  have htrace : WordTrace (prefixWord ++ tailWord_2529333) baseStart_2529333 baseEnd_2529333 := by
    simpa [prefixWord, tailWord_2529333, baseEnd_2529333] using wordTrace_append hprefix tailTrace_2529333
  have hstable : (prefixWord ++ tailWord_2529333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529333).length < 2 ^ (prefixWord ++ tailWord_2529333).sum := by decide
  have hdescent : baseEnd_2529333 < baseStart_2529333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529334 : List Nat := [5, 1, 2, 1, 1, 1, 4, 1, 3, 1, 3]
def baseStart_2529334 : Nat := 118140960795 + 2529334 * 2 ^ 59
def prefixEnd_2529334 : Nat := 4983230072969 + 3 ^ 40 * 2529334 * 2
def baseEnd_2529334 : Nat := 1298764077759312202792811

theorem tailTrace_2529334 : CollatzResearch.WordTrace tailWord_2529334 prefixEnd_2529334 1298764077759312202792811 := by
  unfold tailWord_2529334
  simp only [CollatzResearch.WordTrace]
  refine ⟨5765774363666398043809691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61501593212441579133970037 5765774363666398043809691)
  ·
    refine ⟨8648661545499597065714537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5765774363666398043809691 8648661545499597065714537)
    ·
      refine ⟨6486496159124697799285903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8648661545499597065714537 6486496159124697799285903)
      ·
        refine ⟨9729744238687046698928855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6486496159124697799285903 9729744238687046698928855)
        ·
          refine ⟨14594616358030570048393283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9729744238687046698928855 14594616358030570048393283)
          ·
            refine ⟨21891924537045855072589925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14594616358030570048393283 21891924537045855072589925)
            ·
              refine ⟨4104735850696097826110611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21891924537045855072589925 4104735850696097826110611)
              ·
                refine ⟨6157103776044146739165917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4104735850696097826110611 6157103776044146739165917)
                ·
                  refine ⟨2308913916016555027187219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6157103776044146739165917 2308913916016555027187219)
                  ·
                    refine ⟨3463370874024832540780829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2308913916016555027187219 3463370874024832540780829)
                    ·
                      refine ⟨1298764077759312202792811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3463370874024832540780829 1298764077759312202792811)
                      ·
                        rfl

theorem cell23_2529334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_2529334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2529334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2529334 prefixEnd_2529334 := by exact prefixLift 2529334
  have htrace : WordTrace (prefixWord ++ tailWord_2529334) baseStart_2529334 baseEnd_2529334 := by
    simpa [prefixWord, tailWord_2529334, baseEnd_2529334] using wordTrace_append hprefix tailTrace_2529334
  have hstable : (prefixWord ++ tailWord_2529334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529334).length < 2 ^ (prefixWord ++ tailWord_2529334).sum := by decide
  have hdescent : baseEnd_2529334 < baseStart_2529334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529343 : List Nat := [1, 1, 2, 2, 3, 1, 3, 1, 3, 1, 5]
def baseStart_2529343 : Nat := 118140960795 + 2529343 * 2 ^ 59
def prefixEnd_2529343 : Nat := 4983230072969 + 3 ^ 40 * 2529343 * 2
def baseEnd_2529343 : Nat := 1298768699085202667580269

theorem tailTrace_2529343 : CollatzResearch.WordTrace tailWord_2529343 prefixEnd_2529343 1298768699085202667580269 := by
  unfold tailWord_2529343
  simp only [CollatzResearch.WordTrace]
  refine ⟨92252718075629763238032683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61501812050419842158688455 92252718075629763238032683)
  ·
    refine ⟨138379077113444644857049025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92252718075629763238032683 138379077113444644857049025)
    ·
      refine ⟨103784307835083483642786769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138379077113444644857049025 103784307835083483642786769)
      ·
        refine ⟨77838230876312612732090077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103784307835083483642786769 77838230876312612732090077)
        ·
          refine ⟨29189336578617229774533779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77838230876312612732090077 29189336578617229774533779)
          ·
            refine ⟨43784004867925844661800669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29189336578617229774533779 43784004867925844661800669)
            ·
              refine ⟨16419001825472191748175251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43784004867925844661800669 16419001825472191748175251)
              ·
                refine ⟨24628502738208287622262877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16419001825472191748175251 24628502738208287622262877)
                ·
                  refine ⟨9235688526828107858348579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24628502738208287622262877 9235688526828107858348579)
                  ·
                    refine ⟨13853532790242161787522869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9235688526828107858348579 13853532790242161787522869)
                    ·
                      refine ⟨1298768699085202667580269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13853532790242161787522869 1298768699085202667580269)
                      ·
                        rfl

theorem cell23_2529343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 3, 1, 5].length) (baseStart_2529343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2529343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2529343 prefixEnd_2529343 := by exact prefixLift 2529343
  have htrace : WordTrace (prefixWord ++ tailWord_2529343) baseStart_2529343 baseEnd_2529343 := by
    simpa [prefixWord, tailWord_2529343, baseEnd_2529343] using wordTrace_append hprefix tailTrace_2529343
  have hstable : (prefixWord ++ tailWord_2529343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529343).length < 2 ^ (prefixWord ++ tailWord_2529343).sum := by decide
  have hdescent : baseEnd_2529343 < baseStart_2529343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529353 : List Nat := [1, 2, 1, 1, 2, 2, 5, 1, 1, 1, 6]
def baseStart_2529353 : Nat := 118140960795 + 2529353 * 2 ^ 59
def prefixEnd_2529353 : Nat := 4983230072969 + 3 ^ 40 * 2529353 * 2
def baseEnd_2529353 : Nat := 1298773833891747628455223

theorem tailTrace_2529353 : CollatzResearch.WordTrace tailWord_2529353 prefixEnd_2529353 1298773833891747628455223 := by
  unfold tailWord_2529353
  simp only [CollatzResearch.WordTrace]
  refine ⟨92253082805593534945896713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61502055203729023297264475 92253082805593534945896713)
  ·
    refine ⟨69189812104195151209422535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92253082805593534945896713 69189812104195151209422535)
    ·
      refine ⟨103784718156292726814133803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69189812104195151209422535 103784718156292726814133803)
      ·
        refine ⟨155677077234439090221200705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103784718156292726814133803 155677077234439090221200705)
        ·
          refine ⟨116757807925829317665900529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155677077234439090221200705 116757807925829317665900529)
          ·
            refine ⟨87568355944371988249425397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116757807925829317665900529 87568355944371988249425397)
            ·
              refine ⟨8209533369784873898383631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 87568355944371988249425397 8209533369784873898383631)
              ·
                refine ⟨12314300054677310847575447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8209533369784873898383631 12314300054677310847575447)
                ·
                  refine ⟨18471450082015966271363171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12314300054677310847575447 18471450082015966271363171)
                  ·
                    refine ⟨27707175123023949407044757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18471450082015966271363171 27707175123023949407044757)
                    ·
                      refine ⟨1298773833891747628455223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27707175123023949407044757 1298773833891747628455223)
                      ·
                        rfl

theorem cell23_2529353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 1, 6].length) (baseStart_2529353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2529353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2529353 prefixEnd_2529353 := by exact prefixLift 2529353
  have htrace : WordTrace (prefixWord ++ tailWord_2529353) baseStart_2529353 baseEnd_2529353 := by
    simpa [prefixWord, tailWord_2529353, baseEnd_2529353] using wordTrace_append hprefix tailTrace_2529353
  have hstable : (prefixWord ++ tailWord_2529353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529353).length < 2 ^ (prefixWord ++ tailWord_2529353).sum := by decide
  have hdescent : baseEnd_2529353 < baseStart_2529353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529357 : List Nat := [1, 6, 1, 1, 1, 1, 1, 1, 2, 6, 2]
def baseStart_2529357 : Nat := 118140960795 + 2529357 * 2 ^ 59
def prefixEnd_2529357 : Nat := 4983230072969 + 3 ^ 40 * 2529357 * 2
def baseEnd_2529357 : Nat := 1298775887814365612805205

theorem tailTrace_2529357 : CollatzResearch.WordTrace tailWord_2529357 prefixEnd_2529357 1298775887814365612805205 := by
  unfold tailWord_2529357
  simp only [CollatzResearch.WordTrace]
  refine ⟨92253228697579043629042325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61502152465052695752694883 92253228697579043629042325)
  ·
    refine ⟨4324370095199017670111359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 92253228697579043629042325 4324370095199017670111359)
    ·
      refine ⟨6486555142798526505167039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4324370095199017670111359 6486555142798526505167039)
      ·
        refine ⟨9729832714197789757750559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6486555142798526505167039 9729832714197789757750559)
        ·
          refine ⟨14594749071296684636625839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9729832714197789757750559 14594749071296684636625839)
          ·
            refine ⟨21892123606945026954938759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14594749071296684636625839 21892123606945026954938759)
            ·
              refine ⟨32838185410417540432408139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21892123606945026954938759 32838185410417540432408139)
              ·
                refine ⟨49257278115626310648612209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32838185410417540432408139 49257278115626310648612209)
                ·
                  refine ⟨36942958586719732986459157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49257278115626310648612209 36942958586719732986459157)
                  ·
                    refine ⟨1731701183752487483740273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 36942958586719732986459157 1731701183752487483740273)
                    ·
                      refine ⟨1298775887814365612805205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1731701183752487483740273 1298775887814365612805205)
                      ·
                        rfl

theorem cell23_2529357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_2529357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2529357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2529357 prefixEnd_2529357 := by exact prefixLift 2529357
  have htrace : WordTrace (prefixWord ++ tailWord_2529357) baseStart_2529357 baseEnd_2529357 := by
    simpa [prefixWord, tailWord_2529357, baseEnd_2529357] using wordTrace_append hprefix tailTrace_2529357
  have hstable : (prefixWord ++ tailWord_2529357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529357).length < 2 ^ (prefixWord ++ tailWord_2529357).sum := by decide
  have hdescent : baseEnd_2529357 < baseStart_2529357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529393 : List Nat := [1, 2, 2, 2, 1, 1, 4, 1, 2, 7]
def baseStart_2529393 : Nat := 118140960795 + 2529393 * 2 ^ 59
def prefixEnd_2529393 : Nat := 4983230072969 + 3 ^ 40 * 2529393 * 2
def baseEnd_2529393 : Nat := 432931457705975823985013

theorem tailTrace_2529393 : CollatzResearch.WordTrace tailWord_2529393 prefixEnd_2529393 432931457705975823985013 := by
  unfold tailWord_2529393
  simp only [CollatzResearch.WordTrace]
  refine ⟨92254541725448621777352833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61503027816965747851568555 92254541725448621777352833)
  ·
    refine ⟨69190906294086466333014625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92254541725448621777352833 69190906294086466333014625)
    ·
      refine ⟨51893179720564849749760969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69190906294086466333014625 51893179720564849749760969)
      ·
        refine ⟨38919884790423637312320727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51893179720564849749760969 38919884790423637312320727)
        ·
          refine ⟨58379827185635455968481091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38919884790423637312320727 58379827185635455968481091)
          ·
            refine ⟨87569740778453183952721637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58379827185635455968481091 87569740778453183952721637)
            ·
              refine ⟨16419326395959971991135307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87569740778453183952721637 16419326395959971991135307)
              ·
                refine ⟨24628989593939957986702961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16419326395959971991135307 24628989593939957986702961)
                ·
                  refine ⟨18471742195454968490027221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24628989593939957986702961 18471742195454968490027221)
                  ·
                    refine ⟨432931457705975823985013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18471742195454968490027221 432931457705975823985013)
                    ·
                      rfl

theorem cell23_2529393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 7].length) (baseStart_2529393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2529393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2529393 prefixEnd_2529393 := by exact prefixLift 2529393
  have htrace : WordTrace (prefixWord ++ tailWord_2529393) baseStart_2529393 baseEnd_2529393 := by
    simpa [prefixWord, tailWord_2529393, baseEnd_2529393] using wordTrace_append hprefix tailTrace_2529393
  have hstable : (prefixWord ++ tailWord_2529393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529393).length < 2 ^ (prefixWord ++ tailWord_2529393).sum := by decide
  have hdescent : baseEnd_2529393 < baseStart_2529393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529400 : List Nat := [2, 1, 2, 1, 1, 1, 3, 1, 2, 7, 2]
def baseStart_2529400 : Nat := 118140960795 + 2529400 * 2 ^ 59
def prefixEnd_2529400 : Nat := 4983230072969 + 3 ^ 40 * 2529400 * 2
def baseEnd_2529400 : Nat := 1298797967482508944567507

theorem tailTrace_2529400 : CollatzResearch.WordTrace tailWord_2529400 prefixEnd_2529400 1298797967482508944567507 := by
  unfold tailWord_2529400
  simp only [CollatzResearch.WordTrace]
  refine ⟨46127398518211630986428827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61503198024282174648571769 46127398518211630986428827)
  ·
    refine ⟨69191097777317446479643241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46127398518211630986428827 69191097777317446479643241)
    ·
      refine ⟨51893323332988084859732431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69191097777317446479643241 51893323332988084859732431)
      ·
        refine ⟨77839984999482127289598647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51893323332988084859732431 77839984999482127289598647)
        ·
          refine ⟨116759977499223190934397971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77839984999482127289598647 116759977499223190934397971)
          ·
            refine ⟨175139966248834786401596957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116759977499223190934397971 175139966248834786401596957)
            ·
              refine ⟨65677487343313044900598859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 175139966248834786401596957 65677487343313044900598859)
              ·
                refine ⟨98516231014969567350898289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65677487343313044900598859 98516231014969567350898289)
                ·
                  refine ⟨73887173261227175513173717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98516231014969567350898289 73887173261227175513173717)
                  ·
                    refine ⟨1731730623310011926090009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 73887173261227175513173717 1731730623310011926090009)
                    ·
                      refine ⟨1298797967482508944567507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1731730623310011926090009 1298797967482508944567507)
                      ·
                        rfl

theorem cell23_2529400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 2, 7, 2].length) (baseStart_2529400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2529400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2529400 prefixEnd_2529400 := by exact prefixLift 2529400
  have htrace : WordTrace (prefixWord ++ tailWord_2529400) baseStart_2529400 baseEnd_2529400 := by
    simpa [prefixWord, tailWord_2529400, baseEnd_2529400] using wordTrace_append hprefix tailTrace_2529400
  have hstable : (prefixWord ++ tailWord_2529400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529400).length < 2 ^ (prefixWord ++ tailWord_2529400).sum := by decide
  have hdescent : baseEnd_2529400 < baseStart_2529400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529417 : List Nat := [1, 2, 1, 1, 4, 2, 3, 1, 3, 3, 2]
def baseStart_2529417 : Nat := 118140960795 + 2529417 * 2 ^ 59
def prefixEnd_2529417 : Nat := 4983230072969 + 3 ^ 40 * 2529417 * 2
def baseEnd_2529417 : Nat := 1298806696653635378054929

theorem tailTrace_2529417 : CollatzResearch.WordTrace tailWord_2529417 prefixEnd_2529417 1298806696653635378054929 := by
  unfold tailWord_2529417
  simp only [CollatzResearch.WordTrace]
  refine ⟨92255417077361673876226505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61503611384907782584151003 92255417077361673876226505)
  ·
    refine ⟨69191562808021255407169879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92255417077361673876226505 69191562808021255407169879)
    ·
      refine ⟨103787344212031883110754819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69191562808021255407169879 103787344212031883110754819)
      ·
        refine ⟨155681016318047824666132229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103787344212031883110754819 155681016318047824666132229)
        ·
          refine ⟨29190190559633967124899793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 155681016318047824666132229 29190190559633967124899793)
          ·
            refine ⟨21892642919725475343674845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29190190559633967124899793 21892642919725475343674845)
            ·
              refine ⟨8209741094897053253878067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21892642919725475343674845 8209741094897053253878067)
              ·
                refine ⟨12314611642345579880817101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8209741094897053253878067 12314611642345579880817101)
                ·
                  refine ⟨4617979365879592455306413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12314611642345579880817101 4617979365879592455306413)
                  ·
                    refine ⟨1731742262204847170739905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4617979365879592455306413 1731742262204847170739905)
                    ·
                      refine ⟨1298806696653635378054929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1731742262204847170739905 1298806696653635378054929)
                      ·
                        rfl

theorem cell23_2529417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 3, 3, 2].length) (baseStart_2529417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2529417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2529417 prefixEnd_2529417 := by exact prefixLift 2529417
  have htrace : WordTrace (prefixWord ++ tailWord_2529417) baseStart_2529417 baseEnd_2529417 := by
    simpa [prefixWord, tailWord_2529417, baseEnd_2529417] using wordTrace_append hprefix tailTrace_2529417
  have hstable : (prefixWord ++ tailWord_2529417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529417).length < 2 ^ (prefixWord ++ tailWord_2529417).sum := by decide
  have hdescent : baseEnd_2529417 < baseStart_2529417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529428 : List Nat := [2, 4, 2, 3, 1, 1, 3, 1, 1, 2, 3]
def baseStart_2529428 : Nat := 118140960795 + 2529428 * 2 ^ 59
def prefixEnd_2529428 : Nat := 4983230072969 + 3 ^ 40 * 2529428 * 2
def baseEnd_2529428 : Nat := 1298812344940834835017379

theorem tailTrace_2529428 : CollatzResearch.WordTrace tailWord_2529428 prefixEnd_2529428 1298812344940834835017379 := by
  unfold tailWord_2529428
  simp only [CollatzResearch.WordTrace]
  refine ⟨46127909140160911377438469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61503878853547881836584625 46127909140160911377438469)
  ·
    refine ⟨8648982963780170883269713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46127909140160911377438469 8648982963780170883269713)
    ·
      refine ⟨6486737222835128162452285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8648982963780170883269713 6486737222835128162452285)
      ·
        refine ⟨2432526458563173060919607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6486737222835128162452285 2432526458563173060919607)
        ·
          refine ⟨3648789687844759591379411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2432526458563173060919607 3648789687844759591379411)
          ·
            refine ⟨5473184531767139387069117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3648789687844759591379411 5473184531767139387069117)
            ·
              refine ⟨2052444199412677270150919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5473184531767139387069117 2052444199412677270150919)
              ·
                refine ⟨3078666299119015905226379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2052444199412677270150919 3078666299119015905226379)
                ·
                  refine ⟨4617999448678523857839569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3078666299119015905226379 4617999448678523857839569)
                  ·
                    refine ⟨3463499586508892893379677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4617999448678523857839569 3463499586508892893379677)
                    ·
                      refine ⟨1298812344940834835017379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3463499586508892893379677 1298812344940834835017379)
                      ·
                        rfl

theorem cell23_2529428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_2529428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2529428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2529428 prefixEnd_2529428 := by exact prefixLift 2529428
  have htrace : WordTrace (prefixWord ++ tailWord_2529428) baseStart_2529428 baseEnd_2529428 := by
    simpa [prefixWord, tailWord_2529428, baseEnd_2529428] using wordTrace_append hprefix tailTrace_2529428
  have hstable : (prefixWord ++ tailWord_2529428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529428).length < 2 ^ (prefixWord ++ tailWord_2529428).sum := by decide
  have hdescent : baseEnd_2529428 < baseStart_2529428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529443 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 6]
def baseStart_2529443 : Nat := 118140960795 + 2529443 * 2 ^ 59
def prefixEnd_2529443 : Nat := 4983230072969 + 3 ^ 40 * 2529443 * 2
def baseEnd_2529443 : Nat := 1298820047150652276329809

theorem tailTrace_2529443 : CollatzResearch.WordTrace tailWord_2529443 prefixEnd_2529443 1298820047150652276329809 := by
  unfold tailWord_2529443
  simp only [CollatzResearch.WordTrace]
  refine ⟨92256365375267480316672983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61504243583511653544448655 92256365375267480316672983)
  ·
    refine ⟨138384548062901220475009475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92256365375267480316672983 138384548062901220475009475)
    ·
      refine ⟨207576822094351830712514213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138384548062901220475009475 207576822094351830712514213)
      ·
        refine ⟨38920654142690968258596415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 207576822094351830712514213 38920654142690968258596415)
        ·
          refine ⟨58380981214036452387894623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38920654142690968258596415 58380981214036452387894623)
          ·
            refine ⟨87571471821054678581841935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58380981214036452387894623 87571471821054678581841935)
            ·
              refine ⟨131357207731582017872762903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87571471821054678581841935 131357207731582017872762903)
              ·
                refine ⟨197035811597373026809144355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131357207731582017872762903 197035811597373026809144355)
                ·
                  refine ⟨295553717396059540213716533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 197035811597373026809144355 295553717396059540213716533)
                  ·
                    refine ⟨27708161005880581895035925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 295553717396059540213716533 27708161005880581895035925)
                    ·
                      refine ⟨1298820047150652276329809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27708161005880581895035925 1298820047150652276329809)
                      ·
                        rfl

theorem cell23_2529443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_2529443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2529443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2529443 prefixEnd_2529443 := by exact prefixLift 2529443
  have htrace : WordTrace (prefixWord ++ tailWord_2529443) baseStart_2529443 baseEnd_2529443 := by
    simpa [prefixWord, tailWord_2529443, baseEnd_2529443] using wordTrace_append hprefix tailTrace_2529443
  have hstable : (prefixWord ++ tailWord_2529443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529443).length < 2 ^ (prefixWord ++ tailWord_2529443).sum := by decide
  have hdescent : baseEnd_2529443 < baseStart_2529443 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529457 : List Nat := [1, 2, 2, 5, 2, 1, 1, 1, 2, 6]
def baseStart_2529457 : Nat := 118140960795 + 2529457 * 2 ^ 59
def prefixEnd_2529457 : Nat := 4983230072969 + 3 ^ 40 * 2529457 * 2
def baseEnd_2529457 : Nat := 432942411959938407184915

theorem tailTrace_2529457 : CollatzResearch.WordTrace tailWord_2529457 prefixEnd_2529457 432942411959938407184915 := by
  unfold tailWord_2529457
  simp only [CollatzResearch.WordTrace]
  refine ⟨92256875997216760707682625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61504583998144507138455083 92256875997216760707682625)
  ·
    refine ⟨69192656997912570530761969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92256875997216760707682625 69192656997912570530761969)
    ·
      refine ⟨51894492748434427898071477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69192656997912570530761969 51894492748434427898071477)
      ·
        refine ⟨4865108695165727615444201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51894492748434427898071477 4865108695165727615444201)
        ·
          refine ⟨3648831521374295711583151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4865108695165727615444201 3648831521374295711583151)
          ·
            refine ⟨5473247282061443567374727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3648831521374295711583151 5473247282061443567374727)
            ·
              refine ⟨8209870923092165351062091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5473247282061443567374727 8209870923092165351062091)
              ·
                refine ⟨12314806384638248026593137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8209870923092165351062091 12314806384638248026593137)
                ·
                  refine ⟨9236104788478686019944853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12314806384638248026593137 9236104788478686019944853)
                  ·
                    refine ⟨432942411959938407184915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9236104788478686019944853 432942411959938407184915)
                    ·
                      rfl

theorem cell23_2529457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 2, 6].length) (baseStart_2529457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2529457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2529457 prefixEnd_2529457 := by exact prefixLift 2529457
  have htrace : WordTrace (prefixWord ++ tailWord_2529457) baseStart_2529457 baseEnd_2529457 := by
    simpa [prefixWord, tailWord_2529457, baseEnd_2529457] using wordTrace_append hprefix tailTrace_2529457
  have hstable : (prefixWord ++ tailWord_2529457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529457).length < 2 ^ (prefixWord ++ tailWord_2529457).sum := by decide
  have hdescent : baseEnd_2529457 < baseStart_2529457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529464 : List Nat := [2, 1, 2, 1, 2, 1, 3, 5, 2, 2, 2]
def baseStart_2529464 : Nat := 118140960795 + 2529464 * 2 ^ 59
def prefixEnd_2529464 : Nat := 4983230072969 + 3 ^ 40 * 2529464 * 2
def baseEnd_2529464 : Nat := 1298830830244396694167213

theorem tailTrace_2529464 : CollatzResearch.WordTrace tailWord_2529464 prefixEnd_2529464 1298830830244396694167213 := by
  unfold tailWord_2529464
  simp only [CollatzResearch.WordTrace]
  refine ⟨46128565654095700451593723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61504754205460933935458297 46128565654095700451593723)
  ·
    refine ⟨69192848481143550677390585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46128565654095700451593723 69192848481143550677390585)
    ·
      refine ⟨51894636360857663008042939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69192848481143550677390585 51894636360857663008042939)
      ·
        refine ⟨77841954541286494512064409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51894636360857663008042939 77841954541286494512064409)
        ·
          refine ⟨58381465905964870884048307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77841954541286494512064409 58381465905964870884048307)
          ·
            refine ⟨87572198858947306326072461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58381465905964870884048307 87572198858947306326072461)
            ·
              refine ⟨32839574572105239872277173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87572198858947306326072461 32839574572105239872277173)
              ·
                refine ⟨3078710116134866238025985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32839574572105239872277173 3078710116134866238025985)
                ·
                  refine ⟨2309032587101149678519489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3078710116134866238025985 2309032587101149678519489)
                  ·
                    refine ⟨1731774440325862258889617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2309032587101149678519489 1731774440325862258889617)
                    ·
                      refine ⟨1298830830244396694167213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1731774440325862258889617 1298830830244396694167213)
                      ·
                        rfl

theorem cell23_2529464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 5, 2, 2, 2].length) (baseStart_2529464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2529464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2529464 prefixEnd_2529464 := by exact prefixLift 2529464
  have htrace : WordTrace (prefixWord ++ tailWord_2529464) baseStart_2529464 baseEnd_2529464 := by
    simpa [prefixWord, tailWord_2529464, baseEnd_2529464] using wordTrace_append hprefix tailTrace_2529464
  have hstable : (prefixWord ++ tailWord_2529464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529464).length < 2 ^ (prefixWord ++ tailWord_2529464).sum := by decide
  have hdescent : baseEnd_2529464 < baseStart_2529464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529480 : List Nat := [2, 1, 3, 1, 2, 1, 1, 1, 3, 5, 3]
def baseStart_2529480 : Nat := 118140960795 + 2529480 * 2 ^ 59
def prefixEnd_2529480 : Nat := 4983230072969 + 3 ^ 40 * 2529480 * 2
def baseEnd_2529480 : Nat := 1298839045934868631567139

theorem tailTrace_2529480 : CollatzResearch.WordTrace tailWord_2529480 prefixEnd_2529480 1298839045934868631567139 := by
  unfold tailWord_2529480
  simp only [CollatzResearch.WordTrace]
  refine ⟨46128857438066717817884947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61505143250755623757179929 46128857438066717817884947)
  ·
    refine ⟨69193286157100076726827421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46128857438066717817884947 69193286157100076726827421)
    ·
      refine ⟨25947482308912528772560283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69193286157100076726827421 25947482308912528772560283)
      ·
        refine ⟨38921223463368793158840425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25947482308912528772560283 38921223463368793158840425)
        ·
          refine ⟨29190917597526594869130319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38921223463368793158840425 29190917597526594869130319)
          ·
            refine ⟨43786376396289892303695479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29190917597526594869130319 43786376396289892303695479)
            ·
              refine ⟨65679564594434838455543219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43786376396289892303695479 65679564594434838455543219)
              ·
                refine ⟨98519346891652257683314829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65679564594434838455543219 98519346891652257683314829)
                ·
                  refine ⟨36944755084369596631243061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 98519346891652257683314829 36944755084369596631243061)
                  ·
                    refine ⟨3463570789159649684179037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36944755084369596631243061 3463570789159649684179037)
                    ·
                      refine ⟨1298839045934868631567139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3463570789159649684179037 1298839045934868631567139)
                      ·
                        rfl

theorem cell23_2529480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 3, 5, 3].length) (baseStart_2529480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2529480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2529480 prefixEnd_2529480 := by exact prefixLift 2529480
  have htrace : WordTrace (prefixWord ++ tailWord_2529480) baseStart_2529480 baseEnd_2529480 := by
    simpa [prefixWord, tailWord_2529480, baseEnd_2529480] using wordTrace_append hprefix tailTrace_2529480
  have hstable : (prefixWord ++ tailWord_2529480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529480).length < 2 ^ (prefixWord ++ tailWord_2529480).sum := by decide
  have hdescent : baseEnd_2529480 < baseStart_2529480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529487 : List Nat := [1, 1, 2, 1, 1, 3, 6, 3, 5]
def baseStart_2529487 : Nat := 118140960795 + 2529487 * 2 ^ 59
def prefixEnd_2529487 : Nat := 4983230072969 + 3 ^ 40 * 2529487 * 2
def baseEnd_2529487 : Nat := 144315848922161122686623

theorem tailTrace_2529487 : CollatzResearch.WordTrace tailWord_2529487 prefixEnd_2529487 144315848922161122686623 := by
  unfold tailWord_2529487
  simp only [CollatzResearch.WordTrace]
  refine ⟨92257970187108075831274715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61505313458072050554183143 92257970187108075831274715)
  ·
    refine ⟨138386955280662113746912073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92257970187108075831274715 138386955280662113746912073)
    ·
      refine ⟨103790216460496585310184055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138386955280662113746912073 103790216460496585310184055)
      ·
        refine ⟨155685324690744877965276083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103790216460496585310184055 155685324690744877965276083)
        ·
          refine ⟨233527987036117316947914125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155685324690744877965276083 233527987036117316947914125)
          ·
            refine ⟨87572995138543993855467797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 233527987036117316947914125 87572995138543993855467797)
            ·
              refine ⟨4104984147119249711975053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 87572995138543993855467797 4104984147119249711975053)
              ·
                refine ⟨1539369055169718641990645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4104984147119249711975053 1539369055169718641990645)
                ·
                  refine ⟨144315848922161122686623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1539369055169718641990645 144315848922161122686623)
                  ·
                    rfl

theorem cell23_2529487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 3, 5].length) (baseStart_2529487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2529487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2529487 prefixEnd_2529487 := by exact prefixLift 2529487
  have htrace : WordTrace (prefixWord ++ tailWord_2529487) baseStart_2529487 baseEnd_2529487 := by
    simpa [prefixWord, tailWord_2529487, baseEnd_2529487] using wordTrace_append hprefix tailTrace_2529487
  have hstable : (prefixWord ++ tailWord_2529487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529487).length < 2 ^ (prefixWord ++ tailWord_2529487).sum := by decide
  have hdescent : baseEnd_2529487 < baseStart_2529487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529494 : List Nat := [5, 2, 1, 2, 1, 1, 1, 2, 2, 2, 4]
def baseStart_2529494 : Nat := 118140960795 + 2529494 * 2 ^ 59
def prefixEnd_2529494 : Nat := 4983230072969 + 3 ^ 40 * 2529494 * 2
def baseEnd_2529494 : Nat := 1298846234664031576792075

theorem tailTrace_2529494 : CollatzResearch.WordTrace tailWord_2529494 prefixEnd_2529494 1298846234664031576792075 := by
  unfold tailWord_2529494
  simp only [CollatzResearch.WordTrace]
  refine ⟨5766139093630169751673721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61505483665388477351186357 5766139093630169751673721)
  ·
    refine ⟨4324604320222627313755291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5766139093630169751673721 4324604320222627313755291)
    ·
      refine ⟨6486906480333940970632937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4324604320222627313755291 6486906480333940970632937)
      ·
        refine ⟨4865179860250455727974703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6486906480333940970632937 4865179860250455727974703)
        ·
          refine ⟨7297769790375683591962055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4865179860250455727974703 7297769790375683591962055)
          ·
            refine ⟨10946654685563525387943083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7297769790375683591962055 10946654685563525387943083)
            ·
              refine ⟨16419982028345288081914625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10946654685563525387943083 16419982028345288081914625)
              ·
                refine ⟨12314986521258966061435969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16419982028345288081914625 12314986521258966061435969)
                ·
                  refine ⟨9236239890944224546076977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12314986521258966061435969 9236239890944224546076977)
                  ·
                    refine ⟨6927179918208168409557733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9236239890944224546076977 6927179918208168409557733)
                    ·
                      refine ⟨1298846234664031576792075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6927179918208168409557733 1298846234664031576792075)
                      ·
                        rfl

theorem cell23_2529494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_2529494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2529494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2529494 prefixEnd_2529494 := by exact prefixLift 2529494
  have htrace : WordTrace (prefixWord ++ tailWord_2529494) baseStart_2529494 baseEnd_2529494 := by
    simpa [prefixWord, tailWord_2529494, baseEnd_2529494] using wordTrace_append hprefix tailTrace_2529494
  have hstable : (prefixWord ++ tailWord_2529494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529494).length < 2 ^ (prefixWord ++ tailWord_2529494).sum := by decide
  have hdescent : baseEnd_2529494 < baseStart_2529494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529537 : List Nat := [1, 2, 4, 1, 1, 2, 2, 3, 2, 1, 4]
def baseStart_2529537 : Nat := 118140960795 + 2529537 * 2 ^ 59
def prefixEnd_2529537 : Nat := 4983230072969 + 3 ^ 40 * 2529537 * 2
def baseEnd_2529537 : Nat := 1298868314332174908554377

theorem tailTrace_2529537 : CollatzResearch.WordTrace tailWord_2529537 prefixEnd_2529537 1298868314332174908554377 := by
  unfold tailWord_2529537
  simp only [CollatzResearch.WordTrace]
  refine ⟨92259793836926934370594865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61506529224617956247063243 92259793836926934370594865)
  ·
    refine ⟨69194845377695200777946149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92259793836926934370594865 69194845377695200777946149)
    ·
      refine ⟨12974033508317850145864903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69194845377695200777946149 12974033508317850145864903)
      ·
        refine ⟨19461050262476775218797355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12974033508317850145864903 19461050262476775218797355)
        ·
          refine ⟨29191575393715162828196033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19461050262476775218797355 29191575393715162828196033)
          ·
            refine ⟨21893681545286372121147025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29191575393715162828196033 21893681545286372121147025)
            ·
              refine ⟨16420261158964779090860269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21893681545286372121147025 16420261158964779090860269)
              ·
                refine ⟨6157597934611792159072601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16420261158964779090860269 6157597934611792159072601)
                ·
                  refine ⟨4618198450958844119304451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6157597934611792159072601 4618198450958844119304451)
                  ·
                    refine ⟨6927297676438266178956677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4618198450958844119304451 6927297676438266178956677)
                    ·
                      refine ⟨1298868314332174908554377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6927297676438266178956677 1298868314332174908554377)
                      ·
                        rfl

theorem cell23_2529537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_2529537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2529537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2529537 prefixEnd_2529537 := by exact prefixLift 2529537
  have htrace : WordTrace (prefixWord ++ tailWord_2529537) baseStart_2529537 baseEnd_2529537 := by
    simpa [prefixWord, tailWord_2529537, baseEnd_2529537] using wordTrace_append hprefix tailTrace_2529537
  have hstable : (prefixWord ++ tailWord_2529537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529537).length < 2 ^ (prefixWord ++ tailWord_2529537).sum := by decide
  have hdescent : baseEnd_2529537 < baseStart_2529537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529557 : List Nat := [1, 3, 2, 1, 2, 1, 3, 1, 4, 2, 3]
def baseStart_2529557 : Nat := 118140960795 + 2529557 * 2 ^ 59
def prefixEnd_2529557 : Nat := 4983230072969 + 3 ^ 40 * 2529557 * 2
def baseEnd_2529557 : Nat := 1298878583945264830304285

theorem tailTrace_2529557 : CollatzResearch.WordTrace tailWord_2529557 prefixEnd_2529557 1298878583945264830304285 := by
  unfold tailWord_2529557
  simp only [CollatzResearch.WordTrace]
  refine ⟨92260523296854477786322925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61507015531236318524215283 92260523296854477786322925)
  ·
    refine ⟨34597696236320429169871097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92260523296854477786322925 34597696236320429169871097)
    ·
      refine ⟨25948272177240321877403323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34597696236320429169871097 25948272177240321877403323)
      ·
        refine ⟨38922408265860482816104985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25948272177240321877403323 38922408265860482816104985)
        ·
          refine ⟨29191806199395362112078739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38922408265860482816104985 29191806199395362112078739)
          ·
            refine ⟨43787709299093043168118109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29191806199395362112078739 43787709299093043168118109)
            ·
              refine ⟨16420390987159891188044291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43787709299093043168118109 16420390987159891188044291)
              ·
                refine ⟨24630586480739836782066437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16420390987159891188044291 24630586480739836782066437)
                ·
                  refine ⟨4618234965138719396637457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24630586480739836782066437 4618234965138719396637457)
                  ·
                    refine ⟨3463676223854039547478093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4618234965138719396637457 3463676223854039547478093)
                    ·
                      refine ⟨1298878583945264830304285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3463676223854039547478093 1298878583945264830304285)
                      ·
                        rfl

theorem cell23_2529557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 4, 2, 3].length) (baseStart_2529557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2529557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2529557 prefixEnd_2529557 := by exact prefixLift 2529557
  have htrace : WordTrace (prefixWord ++ tailWord_2529557) baseStart_2529557 baseEnd_2529557 := by
    simpa [prefixWord, tailWord_2529557, baseEnd_2529557] using wordTrace_append hprefix tailTrace_2529557
  have hstable : (prefixWord ++ tailWord_2529557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529557).length < 2 ^ (prefixWord ++ tailWord_2529557).sum := by decide
  have hdescent : baseEnd_2529557 < baseStart_2529557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529560 : List Nat := [2, 1, 2, 3, 1, 2, 1, 3, 8]
def baseStart_2529560 : Nat := 118140960795 + 2529560 * 2 ^ 59
def prefixEnd_2529560 : Nat := 4983230072969 + 3 ^ 40 * 2529560 * 2
def baseEnd_2529560 : Nat := 144320013820803146507419

theorem tailTrace_2529560 : CollatzResearch.WordTrace tailWord_2529560 prefixEnd_2529560 144320013820803146507419 := by
  unfold tailWord_2529560
  simp only [CollatzResearch.WordTrace]
  refine ⟨46130316357921804649341067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61507088477229072865788089 46130316357921804649341067)
  ·
    refine ⟨69195474536882706974011601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46130316357921804649341067 69195474536882706974011601)
    ·
      refine ⟨51896605902662030230508701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69195474536882706974011601 51896605902662030230508701)
      ·
        refine ⟨19461227213498261336440763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51896605902662030230508701 19461227213498261336440763)
        ·
          refine ⟨29191840820247392004661145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19461227213498261336440763 29191840820247392004661145)
          ·
            refine ⟨21893880615185544003495859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29191840820247392004661145 21893880615185544003495859)
            ·
              refine ⟨32840820922778316005243789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21893880615185544003495859 32840820922778316005243789)
              ·
                refine ⟨12315307846041868501966421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32840820922778316005243789 12315307846041868501966421)
                ·
                  refine ⟨144320013820803146507419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12315307846041868501966421 144320013820803146507419)
                  ·
                    rfl

theorem cell23_2529560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 8].length) (baseStart_2529560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2529560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2529560 prefixEnd_2529560 := by exact prefixLift 2529560
  have htrace : WordTrace (prefixWord ++ tailWord_2529560) baseStart_2529560 baseEnd_2529560 := by
    simpa [prefixWord, tailWord_2529560, baseEnd_2529560] using wordTrace_append hprefix tailTrace_2529560
  have hstable : (prefixWord ++ tailWord_2529560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529560).length < 2 ^ (prefixWord ++ tailWord_2529560).sum := by decide
  have hdescent : baseEnd_2529560 < baseStart_2529560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529580 : List Nat := [2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 6]
def baseStart_2529580 : Nat := 118140960795 + 2529580 * 2 ^ 59
def prefixEnd_2529580 : Nat := 4983230072969 + 3 ^ 40 * 2529580 * 2
def baseEnd_2529580 : Nat := 1298890394000318240316679

theorem tailTrace_2529580 : CollatzResearch.WordTrace tailWord_2529580 prefixEnd_2529580 1298890394000318240316679 := by
  unfold tailWord_2529580
  simp only [CollatzResearch.WordTrace]
  refine ⟨46130681087885576357205097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61507574783847435142940129 46130681087885576357205097)
  ·
    refine ⟨34598010815914182267903823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46130681087885576357205097 34598010815914182267903823)
    ·
      refine ⟨51897016223871273401855735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34598010815914182267903823 51897016223871273401855735)
      ·
        refine ⟨77845524335806910102783603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51897016223871273401855735 77845524335806910102783603)
        ·
          refine ⟨116768286503710365154175405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77845524335806910102783603 116768286503710365154175405)
          ·
            refine ⟨43788107438891386932815777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116768286503710365154175405 43788107438891386932815777)
            ·
              refine ⟨32841080579168540199611833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43788107438891386932815777 32841080579168540199611833)
              ·
                refine ⟨24630810434376405149708875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32841080579168540199611833 24630810434376405149708875)
                ·
                  refine ⟨36946215651564607724563313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24630810434376405149708875 36946215651564607724563313)
                  ·
                    refine ⟨27709661738673455793422485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36946215651564607724563313 27709661738673455793422485)
                    ·
                      refine ⟨1298890394000318240316679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27709661738673455793422485 1298890394000318240316679)
                      ·
                        rfl

theorem cell23_2529580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 6].length) (baseStart_2529580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2529580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2529580 prefixEnd_2529580 := by exact prefixLift 2529580
  have htrace : WordTrace (prefixWord ++ tailWord_2529580) baseStart_2529580 baseEnd_2529580 := by
    simpa [prefixWord, tailWord_2529580, baseEnd_2529580] using wordTrace_append hprefix tailTrace_2529580
  have hstable : (prefixWord ++ tailWord_2529580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529580).length < 2 ^ (prefixWord ++ tailWord_2529580).sum := by decide
  have hdescent : baseEnd_2529580 < baseStart_2529580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529600 : List Nat := [2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 5]
def baseStart_2529600 : Nat := 118140960795 + 2529600 * 2 ^ 59
def prefixEnd_2529600 : Nat := 4983230072969 + 3 ^ 40 * 2529600 * 2
def baseEnd_2529600 : Nat := 1298900663613408162066587

theorem tailTrace_2529600 : CollatzResearch.WordTrace tailWord_2529600 prefixEnd_2529600 1298900663613408162066587 := by
  unfold tailWord_2529600
  simp only [CollatzResearch.WordTrace]
  refine ⟨46131045817849348065069127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61508061090465797420092169 46131045817849348065069127)
  ·
    refine ⟨69196568726774022097603691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46131045817849348065069127 69196568726774022097603691)
    ·
      refine ⟨103794853090161033146405537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69196568726774022097603691 103794853090161033146405537)
      ·
        refine ⟨77846139817620774859804153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103794853090161033146405537 77846139817620774859804153)
        ·
          refine ⟨58384604863215581144853115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77846139817620774859804153 58384604863215581144853115)
          ·
            refine ⟨87576907294823371717279673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58384604863215581144853115 87576907294823371717279673)
            ·
              refine ⟨65682680471117528787959755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87576907294823371717279673 65682680471117528787959755)
              ·
                refine ⟨98524020706676293181939633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65682680471117528787959755 98524020706676293181939633)
                ·
                  refine ⟨73893015530007219886454725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98524020706676293181939633 73893015530007219886454725)
                  ·
                    refine ⟨13854940411876353728710261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 73893015530007219886454725 13854940411876353728710261)
                    ·
                      refine ⟨1298900663613408162066587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13854940411876353728710261 1298900663613408162066587)
                      ·
                        rfl

theorem cell23_2529600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 5].length) (baseStart_2529600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2529600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2529600 prefixEnd_2529600 := by exact prefixLift 2529600
  have htrace : WordTrace (prefixWord ++ tailWord_2529600) baseStart_2529600 baseEnd_2529600 := by
    simpa [prefixWord, tailWord_2529600, baseEnd_2529600] using wordTrace_append hprefix tailTrace_2529600
  have hstable : (prefixWord ++ tailWord_2529600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529600).length < 2 ^ (prefixWord ++ tailWord_2529600).sum := by decide
  have hdescent : baseEnd_2529600 < baseStart_2529600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529614 : List Nat := [4, 1, 1, 1, 1, 1, 2, 3, 4, 3, 2]
def baseStart_2529614 : Nat := 118140960795 + 2529614 * 2 ^ 59
def prefixEnd_2529614 : Nat := 4983230072969 + 3 ^ 40 * 2529614 * 2
def baseEnd_2529614 : Nat := 1298907852342571107291523

theorem tailTrace_2529614 : CollatzResearch.WordTrace tailWord_2529614 prefixEnd_2529614 1298907852342571107291523 := by
  unfold tailWord_2529614
  simp only [CollatzResearch.WordTrace]
  refine ⟨11532825282205997065143487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61508401505098651014098597 11532825282205997065143487)
  ·
    refine ⟨17299237923308995597715231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11532825282205997065143487 17299237923308995597715231)
    ·
      refine ⟨25948856884963493396572847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17299237923308995597715231 25948856884963493396572847)
      ·
        refine ⟨38923285327445240094859271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25948856884963493396572847 38923285327445240094859271)
        ·
          refine ⟨58384927991167860142288907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38923285327445240094859271 58384927991167860142288907)
          ·
            refine ⟨87577391986751790213433361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58384927991167860142288907 87577391986751790213433361)
            ·
              refine ⟨65683043990063842660075021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87577391986751790213433361 65683043990063842660075021)
              ·
                refine ⟨24631141496273940997528133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65683043990063842660075021 24631141496273940997528133)
                ·
                  refine ⟨4618339030551363937036525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24631141496273940997528133 4618339030551363937036525)
                  ·
                    refine ⟨1731877136456761476388697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4618339030551363937036525 1731877136456761476388697)
                    ·
                      refine ⟨1298907852342571107291523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1731877136456761476388697 1298907852342571107291523)
                      ·
                        rfl

theorem cell23_2529614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 4, 3, 2].length) (baseStart_2529614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2529614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2529614 prefixEnd_2529614 := by exact prefixLift 2529614
  have htrace : WordTrace (prefixWord ++ tailWord_2529614) baseStart_2529614 baseEnd_2529614 := by
    simpa [prefixWord, tailWord_2529614, baseEnd_2529614] using wordTrace_append hprefix tailTrace_2529614
  have hstable : (prefixWord ++ tailWord_2529614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529614).length < 2 ^ (prefixWord ++ tailWord_2529614).sum := by decide
  have hdescent : baseEnd_2529614 < baseStart_2529614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529637 : List Nat := [1, 3, 1, 3, 1, 3, 1, 3, 1, 6]
def baseStart_2529637 : Nat := 118140960795 + 2529637 * 2 ^ 59
def prefixEnd_2529637 : Nat := 4983230072969 + 3 ^ 40 * 2529637 * 2
def baseEnd_2529637 : Nat := 432973220799208172434639

theorem tailTrace_2529637 : CollatzResearch.WordTrace tailWord_2529637 prefixEnd_2529637 432973220799208172434639 := by
  unfold tailWord_2529637
  simp only [CollatzResearch.WordTrace]
  refine ⟨92263441136564651449235165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61508960757709767632823443 92263441136564651449235165)
  ·
    refine ⟨34598790426211744293463187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92263441136564651449235165 34598790426211744293463187)
    ·
      refine ⟨51898185639317616440194781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34598790426211744293463187 51898185639317616440194781)
      ·
        refine ⟨19461819614744106165073043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51898185639317616440194781 19461819614744106165073043)
        ·
          refine ⟨29192729422116159247609565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19461819614744106165073043 29192729422116159247609565)
          ·
            refine ⟨10947273533293559717853587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29192729422116159247609565 10947273533293559717853587)
            ·
              refine ⟨16420910299940339576780381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10947273533293559717853587 16420910299940339576780381)
              ·
                refine ⟨6157841362477627341292643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16420910299940339576780381 6157841362477627341292643)
                ·
                  refine ⟨9236762043716441011938965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6157841362477627341292643 9236762043716441011938965)
                  ·
                    refine ⟨432973220799208172434639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9236762043716441011938965 432973220799208172434639)
                    ·
                      rfl

theorem cell23_2529637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3, 1, 6].length) (baseStart_2529637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2529637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2529637 prefixEnd_2529637 := by exact prefixLift 2529637
  have htrace : WordTrace (prefixWord ++ tailWord_2529637) baseStart_2529637 baseEnd_2529637 := by
    simpa [prefixWord, tailWord_2529637, baseEnd_2529637] using wordTrace_append hprefix tailTrace_2529637
  have hstable : (prefixWord ++ tailWord_2529637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529637).length < 2 ^ (prefixWord ++ tailWord_2529637).sum := by decide
  have hdescent : baseEnd_2529637 < baseStart_2529637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529661 : List Nat := [1, 4, 1, 1, 2, 3, 4, 1, 1, 1, 4]
def baseStart_2529661 : Nat := 118140960795 + 2529661 * 2 ^ 59
def prefixEnd_2529661 : Nat := 4983230072969 + 3 ^ 40 * 2529661 * 2
def baseEnd_2529661 : Nat := 1298931985933332423403807

theorem tailTrace_2529661 : CollatzResearch.WordTrace tailWord_2529661 prefixEnd_2529661 1298931985933332423403807 := by
  unfold tailWord_2529661
  simp only [CollatzResearch.WordTrace]
  refine ⟨92264316488477703548108837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61509544325651802365405891 92264316488477703548108837)
  ·
    refine ⟨17299559341589569415270407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92264316488477703548108837 17299559341589569415270407)
    ·
      refine ⟨25949339012384354122905611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17299559341589569415270407 25949339012384354122905611)
      ·
        refine ⟨38924008518576531184358417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25949339012384354122905611 38924008518576531184358417)
        ·
          refine ⟨29193006388932398388268813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38924008518576531184358417 29193006388932398388268813)
          ·
            refine ⟨10947377395849649395600805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29193006388932398388268813 10947377395849649395600805)
            ·
              refine ⟨2052633261721809261675151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10947377395849649395600805 2052633261721809261675151)
              ·
                refine ⟨3078949892582713892512727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2052633261721809261675151 3078949892582713892512727)
                ·
                  refine ⟨4618424838874070838769091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3078949892582713892512727 4618424838874070838769091)
                  ·
                    refine ⟨6927637258311106258153637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4618424838874070838769091 6927637258311106258153637)
                    ·
                      refine ⟨1298931985933332423403807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6927637258311106258153637 1298931985933332423403807)
                      ·
                        rfl

theorem cell23_2529661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4, 1, 1, 1, 4].length) (baseStart_2529661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2529661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2529661 prefixEnd_2529661 := by exact prefixLift 2529661
  have htrace : WordTrace (prefixWord ++ tailWord_2529661) baseStart_2529661 baseEnd_2529661 := by
    simpa [prefixWord, tailWord_2529661, baseEnd_2529661] using wordTrace_append hprefix tailTrace_2529661
  have hstable : (prefixWord ++ tailWord_2529661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529661).length < 2 ^ (prefixWord ++ tailWord_2529661).sum := by decide
  have hdescent : baseEnd_2529661 < baseStart_2529661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529667 : List Nat := [1, 1, 1, 3, 6, 1, 10]
def baseStart_2529667 : Nat := 118140960795 + 2529667 * 2 ^ 59
def prefixEnd_2529667 : Nat := 4983230072969 + 3 ^ 40 * 2529667 * 2
def baseEnd_2529667 : Nat := 16036235392805671604059

theorem tailTrace_2529667 : CollatzResearch.WordTrace tailWord_2529667 prefixEnd_2529667 16036235392805671604059 := by
  unfold tailWord_2529667
  simp only [CollatzResearch.WordTrace]
  refine ⟨92264535326455966572827255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61509690217637311048551503 92264535326455966572827255)
  ·
    refine ⟨138396802989683949859240883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92264535326455966572827255 138396802989683949859240883)
    ·
      refine ⟨207595204484525924788861325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138396802989683949859240883 207595204484525924788861325)
      ·
        refine ⟨77848201681697221795822997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 207595204484525924788861325 77848201681697221795822997)
        ·
          refine ⟨3649134453829557271679203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 77848201681697221795822997 3649134453829557271679203)
          ·
            refine ⟨5473701680744335907518805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3649134453829557271679203 5473701680744335907518805)
            ·
              refine ⟨16036235392805671604059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5473701680744335907518805 16036235392805671604059)
              ·
                rfl

theorem cell23_2529667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 10].length) (baseStart_2529667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2529667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2529667 prefixEnd_2529667 := by exact prefixLift 2529667
  have htrace : WordTrace (prefixWord ++ tailWord_2529667) baseStart_2529667 baseEnd_2529667 := by
    simpa [prefixWord, tailWord_2529667, baseEnd_2529667] using wordTrace_append hprefix tailTrace_2529667
  have hstable : (prefixWord ++ tailWord_2529667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529667).length < 2 ^ (prefixWord ++ tailWord_2529667).sum := by decide
  have hdescent : baseEnd_2529667 < baseStart_2529667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529678 : List Nat := [4, 1, 1, 4, 1, 1, 1, 3, 3, 2, 2]
def baseStart_2529678 : Nat := 118140960795 + 2529678 * 2 ^ 59
def prefixEnd_2529678 : Nat := 4983230072969 + 3 ^ 40 * 2529678 * 2
def baseEnd_2529678 : Nat := 1298940715104458856891229

theorem tailTrace_2529678 : CollatzResearch.WordTrace tailWord_2529678 prefixEnd_2529678 1298940715104458856891229 := by
  unfold tailWord_2529678
  simp only [CollatzResearch.WordTrace]
  refine ⟨11533117066177014431434711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61509957686277410300985125 11533117066177014431434711)
  ·
    refine ⟨17299675599265521647152067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11533117066177014431434711 17299675599265521647152067)
    ·
      refine ⟨25949513398898282470728101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17299675599265521647152067 25949513398898282470728101)
      ·
        refine ⟨4865533762293427963261519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25949513398898282470728101 4865533762293427963261519)
        ·
          refine ⟨7298300643440141944892279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4865533762293427963261519 7298300643440141944892279)
          ·
            refine ⟨10947450965160212917338419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7298300643440141944892279 10947450965160212917338419)
            ·
              refine ⟨16421176447740319376007629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10947450965160212917338419 16421176447740319376007629)
              ·
                refine ⟨6157941167902619766002861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16421176447740319376007629 6157941167902619766002861)
                ·
                  refine ⟨2309227937963482412251073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6157941167902619766002861 2309227937963482412251073)
                  ·
                    refine ⟨1731920953472611809188305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2309227937963482412251073 1731920953472611809188305)
                    ·
                      refine ⟨1298940715104458856891229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1731920953472611809188305 1298940715104458856891229)
                      ·
                        rfl

theorem cell23_2529678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_2529678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2529678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2529678 prefixEnd_2529678 := by exact prefixLift 2529678
  have htrace : WordTrace (prefixWord ++ tailWord_2529678) baseStart_2529678 baseEnd_2529678 := by
    simpa [prefixWord, tailWord_2529678, baseEnd_2529678] using wordTrace_append hprefix tailTrace_2529678
  have hstable : (prefixWord ++ tailWord_2529678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529678).length < 2 ^ (prefixWord ++ tailWord_2529678).sum := by decide
  have hdescent : baseEnd_2529678 < baseStart_2529678 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529688 : List Nat := [2, 1, 2, 5, 1, 2, 3, 1, 2, 4]
def baseStart_2529688 : Nat := 118140960795 + 2529688 * 2 ^ 59
def prefixEnd_2529688 : Nat := 4983230072969 + 3 ^ 40 * 2529688 * 2
def baseEnd_2529688 : Nat := 432981949970334605922061

theorem tailTrace_2529688 : CollatzResearch.WordTrace tailWord_2529688 prefixEnd_2529688 432981949970334605922061 := by
  unfold tailWord_2529688
  simp only [CollatzResearch.WordTrace]
  refine ⟨46132650629689943579670859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61510200839586591439561145 46132650629689943579670859)
  ·
    refine ⟨69198975944534915369506289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46132650629689943579670859 69198975944534915369506289)
    ·
      refine ⟨51899231958401186527129717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69198975944534915369506289 51899231958401186527129717)
      ·
        refine ⟨4865552996100111236918411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51899231958401186527129717 4865552996100111236918411)
        ·
          refine ⟨7298329494150166855377617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4865552996100111236918411 7298329494150166855377617)
          ·
            refine ⟨5473747120612625141533213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7298329494150166855377617 5473747120612625141533213)
            ·
              refine ⟨2052655170229734428074955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5473747120612625141533213 2052655170229734428074955)
              ·
                refine ⟨3078982755344601642112433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2052655170229734428074955 3078982755344601642112433)
                ·
                  refine ⟨2309237066508451231584325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3078982755344601642112433 2309237066508451231584325)
                  ·
                    refine ⟨432981949970334605922061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2309237066508451231584325 432981949970334605922061)
                    ·
                      rfl

theorem cell23_2529688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3, 1, 2, 4].length) (baseStart_2529688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2529688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2529688 prefixEnd_2529688 := by exact prefixLift 2529688
  have htrace : WordTrace (prefixWord ++ tailWord_2529688) baseStart_2529688 baseEnd_2529688 := by
    simpa [prefixWord, tailWord_2529688, baseEnd_2529688] using wordTrace_append hprefix tailTrace_2529688
  have hstable : (prefixWord ++ tailWord_2529688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529688).length < 2 ^ (prefixWord ++ tailWord_2529688).sum := by decide
  have hdescent : baseEnd_2529688 < baseStart_2529688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529706 : List Nat := [3, 1, 6, 1, 2, 1, 1, 3, 1, 1, 3]
def baseStart_2529706 : Nat := 118140960795 + 2529706 * 2 ^ 59
def prefixEnd_2529706 : Nat := 4983230072969 + 3 ^ 40 * 2529706 * 2
def baseEnd_2529706 : Nat := 1298955092562784747341101

theorem tailTrace_2529706 : CollatzResearch.WordTrace tailWord_2529706 prefixEnd_2529706 1298955092562784747341101 := by
  unfold tailWord_2529706
  simp only [CollatzResearch.WordTrace]
  refine ⟨23066489443328669058374243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61510638515543117488997981 23066489443328669058374243)
  ·
    refine ⟨34599734164993003587561365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23066489443328669058374243 34599734164993003587561365)
    ·
      refine ⟨1621862538984047043166939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 34599734164993003587561365 1621862538984047043166939)
      ·
        refine ⟨2432793808476070564750409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1621862538984047043166939 2432793808476070564750409)
        ·
          refine ⟨1824595356357052923562807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2432793808476070564750409 1824595356357052923562807)
          ·
            refine ⟨2736893034535579385344211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1824595356357052923562807 2736893034535579385344211)
            ·
              refine ⟨4105339551803369078016317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2736893034535579385344211 4105339551803369078016317)
              ·
                refine ⟨1539502331926263404256119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4105339551803369078016317 1539502331926263404256119)
                ·
                  refine ⟨2309253497889395106384179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1539502331926263404256119 2309253497889395106384179)
                  ·
                    refine ⟨3463880246834092659576269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2309253497889395106384179 3463880246834092659576269)
                    ·
                      refine ⟨1298955092562784747341101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3463880246834092659576269 1298955092562784747341101)
                      ·
                        rfl

theorem cell23_2529706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_2529706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2529706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2529706 prefixEnd_2529706 := by exact prefixLift 2529706
  have htrace : WordTrace (prefixWord ++ tailWord_2529706) baseStart_2529706 baseEnd_2529706 := by
    simpa [prefixWord, tailWord_2529706, baseEnd_2529706] using wordTrace_append hprefix tailTrace_2529706
  have hstable : (prefixWord ++ tailWord_2529706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529706).length < 2 ^ (prefixWord ++ tailWord_2529706).sum := by decide
  have hdescent : baseEnd_2529706 < baseStart_2529706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529729 : List Nat := [1, 2, 7, 1, 1, 2, 1, 1, 3, 2, 2]
def baseStart_2529729 : Nat := 118140960795 + 2529729 * 2 ^ 59
def prefixEnd_2529729 : Nat := 4983230072969 + 3 ^ 40 * 2529729 * 2
def baseEnd_2529729 : Nat := 1298966902617838157353495

theorem tailTrace_2529729 : CollatzResearch.WordTrace tailWord_2529729 prefixEnd_2529729 1298966902617838157353495 := by
  unfold tailWord_2529729
  simp only [CollatzResearch.WordTrace]
  refine ⟨92266796652231351161584241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61511197768154234107722827 92266796652231351161584241)
  ·
    refine ⟨69200097489173513371188181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92266796652231351161584241 69200097489173513371188181)
    ·
      refine ⟨1621877284902504219637223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 69200097489173513371188181 1621877284902504219637223)
      ·
        refine ⟨2432815927353756329455835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1621877284902504219637223 2432815927353756329455835)
        ·
          refine ⟨3649223891030634494183753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2432815927353756329455835 3649223891030634494183753)
          ·
            refine ⟨2736917918272975870637815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3649223891030634494183753 2736917918272975870637815)
            ·
              refine ⟨4105376877409463805956723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2736917918272975870637815 4105376877409463805956723)
              ·
                refine ⟨6158065316114195708935085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4105376877409463805956723 6158065316114195708935085)
                ·
                  refine ⟨2309274493542823390850657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6158065316114195708935085 2309274493542823390850657)
                  ·
                    refine ⟨1731955870157117543137993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2309274493542823390850657 1731955870157117543137993)
                    ·
                      refine ⟨1298966902617838157353495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1731955870157117543137993 1298966902617838157353495)
                      ·
                        rfl

theorem cell23_2529729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_2529729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2529729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2529729 prefixEnd_2529729 := by exact prefixLift 2529729
  have htrace : WordTrace (prefixWord ++ tailWord_2529729) baseStart_2529729 baseEnd_2529729 := by
    simpa [prefixWord, tailWord_2529729, baseEnd_2529729] using wordTrace_append hprefix tailTrace_2529729
  have hstable : (prefixWord ++ tailWord_2529729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529729).length < 2 ^ (prefixWord ++ tailWord_2529729).sum := by decide
  have hdescent : baseEnd_2529729 < baseStart_2529729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529747 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 8, 2, 4]
def baseStart_2529747 : Nat := 118140960795 + 2529747 * 2 ^ 59
def prefixEnd_2529747 : Nat := 4983230072969 + 3 ^ 40 * 2529747 * 2
def baseEnd_2529747 : Nat := 1298976145269619086928411

theorem tailTrace_2529747 : CollatzResearch.WordTrace tailWord_2529747 prefixEnd_2529747 1298976145269619086928411 := by
  unfold tailWord_2529747
  simp only [CollatzResearch.WordTrace]
  refine ⟨92267453166166140235739495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61511635444110760157159663 92267453166166140235739495)
  ·
    refine ⟨138401179749249210353609243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92267453166166140235739495 138401179749249210353609243)
    ·
      refine ⟨207601769623873815530413865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138401179749249210353609243 207601769623873815530413865)
      ·
        refine ⟨155701327217905361647810399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207601769623873815530413865 155701327217905361647810399)
        ·
          refine ⟨233551990826858042471715599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155701327217905361647810399 233551990826858042471715599)
          ·
            refine ⟨350327986240287063707573399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233551990826858042471715599 350327986240287063707573399)
            ·
              refine ⟨525491979360430595561360099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 350327986240287063707573399 525491979360430595561360099)
              ·
                refine ⟨788237969040645893342040149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 525491979360430595561360099 788237969040645893342040149)
                ·
                  refine ⟨9237163699695069062602033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 788237969040645893342040149 9237163699695069062602033)
                  ·
                    refine ⟨6927872774771301796951525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9237163699695069062602033 6927872774771301796951525)
                    ·
                      refine ⟨1298976145269619086928411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6927872774771301796951525 1298976145269619086928411)
                      ·
                        rfl

theorem cell23_2529747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8, 2, 4].length) (baseStart_2529747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2529747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2529747 prefixEnd_2529747 := by exact prefixLift 2529747
  have htrace : WordTrace (prefixWord ++ tailWord_2529747) baseStart_2529747 baseEnd_2529747 := by
    simpa [prefixWord, tailWord_2529747, baseEnd_2529747] using wordTrace_append hprefix tailTrace_2529747
  have hstable : (prefixWord ++ tailWord_2529747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529747).length < 2 ^ (prefixWord ++ tailWord_2529747).sum := by decide
  have hdescent : baseEnd_2529747 < baseStart_2529747 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529784 : List Nat := [2, 1, 2, 1, 1, 4, 2, 2, 2, 3, 3]
def baseStart_2529784 : Nat := 118140960795 + 2529784 * 2 ^ 59
def prefixEnd_2529784 : Nat := 4983230072969 + 3 ^ 40 * 2529784 * 2
def baseEnd_2529784 : Nat := 1298995144053835442165741

theorem tailTrace_2529784 : CollatzResearch.WordTrace tailWord_2529784 prefixEnd_2529784 1298995144053835442165741 := by
  unfold tailWord_2529784
  simp only [CollatzResearch.WordTrace]
  refine ⟨46134401333516047777418203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61512535111354730369890937 46134401333516047777418203)
  ·
    refine ⟨69201602000274071666127305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46134401333516047777418203 69201602000274071666127305)
    ·
      refine ⟨51901201500205553749595479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69201602000274071666127305 51901201500205553749595479)
      ·
        refine ⟨77851802250308330624393219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51901201500205553749595479 77851802250308330624393219)
        ·
          refine ⟨116777703375462495936589829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77851802250308330624393219 116777703375462495936589829)
          ·
            refine ⟨21895819382899217988110593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 116777703375462495936589829 21895819382899217988110593)
            ·
              refine ⟨16421864537174413491082945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21895819382899217988110593 16421864537174413491082945)
              ·
                refine ⟨12316398402880810118312209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16421864537174413491082945 12316398402880810118312209)
                ·
                  refine ⟨9237298802160607588734157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12316398402880810118312209 9237298802160607588734157)
                  ·
                    refine ⟨3463987050810227845775309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9237298802160607588734157 3463987050810227845775309)
                    ·
                      refine ⟨1298995144053835442165741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3463987050810227845775309 1298995144053835442165741)
                      ·
                        rfl

theorem cell23_2529784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 2, 3, 3].length) (baseStart_2529784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2529784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2529784 prefixEnd_2529784 := by exact prefixLift 2529784
  have htrace : WordTrace (prefixWord ++ tailWord_2529784) baseStart_2529784 baseEnd_2529784 := by
    simpa [prefixWord, tailWord_2529784, baseEnd_2529784] using wordTrace_append hprefix tailTrace_2529784
  have hstable : (prefixWord ++ tailWord_2529784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529784).length < 2 ^ (prefixWord ++ tailWord_2529784).sum := by decide
  have hdescent : baseEnd_2529784 < baseStart_2529784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529817 : List Nat := [1, 2, 1, 2, 1, 1, 2, 3, 2, 8]
def baseStart_2529817 : Nat := 118140960795 + 2529817 * 2 ^ 59
def prefixEnd_2529817 : Nat := 4983230072969 + 3 ^ 40 * 2529817 * 2
def baseEnd_2529817 : Nat := 433004029638477937684363

theorem tailTrace_2529817 : CollatzResearch.WordTrace tailWord_2529817 prefixEnd_2529817 433004029638477937684363 := by
  unfold tailWord_2529817
  simp only [CollatzResearch.WordTrace]
  refine ⟨92270006275912542190787705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61513337517275028127191803 92270006275912542190787705)
  ·
    refine ⟨69202504706934406643090779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92270006275912542190787705 69202504706934406643090779)
    ·
      refine ⟨103803757060401609964636169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69202504706934406643090779 103803757060401609964636169)
      ·
        refine ⟨77852817795301207473477127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103803757060401609964636169 77852817795301207473477127)
        ·
          refine ⟨116779226692951811210215691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77852817795301207473477127 116779226692951811210215691)
          ·
            refine ⟨175168840039427716815323537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116779226692951811210215691 175168840039427716815323537)
            ·
              refine ⟨131376630029570787611492653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175168840039427716815323537 131376630029570787611492653)
              ·
                refine ⟨49266236261089045354309745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 131376630029570787611492653 49266236261089045354309745)
                ·
                  refine ⟨36949677195816784015732309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49266236261089045354309745 36949677195816784015732309)
                  ·
                    refine ⟨433004029638477937684363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 36949677195816784015732309 433004029638477937684363)
                    ·
                      rfl

theorem cell23_2529817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 8].length) (baseStart_2529817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2529817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2529817 prefixEnd_2529817 := by exact prefixLift 2529817
  have htrace : WordTrace (prefixWord ++ tailWord_2529817) baseStart_2529817 baseEnd_2529817 := by
    simpa [prefixWord, tailWord_2529817, baseEnd_2529817] using wordTrace_append hprefix tailTrace_2529817
  have hstable : (prefixWord ++ tailWord_2529817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529817).length < 2 ^ (prefixWord ++ tailWord_2529817).sum := by decide
  have hdescent : baseEnd_2529817 < baseStart_2529817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529821 : List Nat := [1, 4, 2, 2, 1, 2, 3, 1, 2, 5]
def baseStart_2529821 : Nat := 118140960795 + 2529821 * 2 ^ 59
def prefixEnd_2529821 : Nat := 4983230072969 + 3 ^ 40 * 2529821 * 2
def baseEnd_2529821 : Nat := 433004714279350599134357

theorem tailTrace_2529821 : CollatzResearch.WordTrace tailWord_2529821 prefixEnd_2529821 433004714279350599134357 := by
  unfold tailWord_2529821
  simp only [CollatzResearch.WordTrace]
  refine ⟨92270152167898050873933317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61513434778598700582622211 92270152167898050873933317)
  ·
    refine ⟨17300653531480884538862497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92270152167898050873933317 17300653531480884538862497)
    ·
      refine ⟨12975490148610663404146873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17300653531480884538862497 12975490148610663404146873)
      ·
        refine ⟨9731617611457997553110155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12975490148610663404146873 9731617611457997553110155)
        ·
          refine ⟨14597426417186996329665233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9731617611457997553110155 14597426417186996329665233)
          ·
            refine ⟨10948069812890247247248925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14597426417186996329665233 10948069812890247247248925)
            ·
              refine ⟨4105526179833842717718347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10948069812890247247248925 4105526179833842717718347)
              ·
                refine ⟨6158289269750764076577521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4105526179833842717718347 6158289269750764076577521)
                ·
                  refine ⟨4618716952313073057433141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6158289269750764076577521 4618716952313073057433141)
                  ·
                    refine ⟨433004714279350599134357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4618716952313073057433141 433004714279350599134357)
                    ·
                      rfl

theorem cell23_2529821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_2529821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2529821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2529821 prefixEnd_2529821 := by exact prefixLift 2529821
  have htrace : WordTrace (prefixWord ++ tailWord_2529821) baseStart_2529821 baseEnd_2529821 := by
    simpa [prefixWord, tailWord_2529821, baseEnd_2529821] using wordTrace_append hprefix tailTrace_2529821
  have hstable : (prefixWord ++ tailWord_2529821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529821).length < 2 ^ (prefixWord ++ tailWord_2529821).sum := by decide
  have hdescent : baseEnd_2529821 < baseStart_2529821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529841 : List Nat := [1, 2, 2, 3, 1, 1, 3, 2, 2, 4, 2]
def baseStart_2529841 : Nat := 118140960795 + 2529841 * 2 ^ 59
def prefixEnd_2529841 : Nat := 4983230072969 + 3 ^ 40 * 2529841 * 2
def baseEnd_2529841 : Nat := 1299024412451141719152979

theorem tailTrace_2529841 : CollatzResearch.WordTrace tailWord_2529841 prefixEnd_2529841 1299024412451141719152979 := by
  unfold tailWord_2529841
  simp only [CollatzResearch.WordTrace]
  refine ⟨92270881627825594289661377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61513921085217062859774251 92270881627825594289661377)
  ·
    refine ⟨69203161220869195717246033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92270881627825594289661377 69203161220869195717246033)
    ·
      refine ⟨51902370915651896787934525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69203161220869195717246033 51902370915651896787934525)
      ·
        refine ⟨19463389093369461295475447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51902370915651896787934525 19463389093369461295475447)
        ·
          refine ⟨29195083640054191943213171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19463389093369461295475447 29195083640054191943213171)
          ·
            refine ⟨43792625460081287914819757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29195083640054191943213171 43792625460081287914819757)
            ·
              refine ⟨16422234547530482968057409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43792625460081287914819757 16422234547530482968057409)
              ·
                refine ⟨12316675910647862226043057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16422234547530482968057409 12316675910647862226043057)
                ·
                  refine ⟨9237506932985896669532293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12316675910647862226043057 9237506932985896669532293)
                  ·
                    refine ⟨1732032549934855625537305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9237506932985896669532293 1732032549934855625537305)
                    ·
                      refine ⟨1299024412451141719152979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1732032549934855625537305 1299024412451141719152979)
                      ·
                        rfl

theorem cell23_2529841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 2, 4, 2].length) (baseStart_2529841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2529841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2529841 prefixEnd_2529841 := by exact prefixLift 2529841
  have htrace : WordTrace (prefixWord ++ tailWord_2529841) baseStart_2529841 baseEnd_2529841 := by
    simpa [prefixWord, tailWord_2529841, baseEnd_2529841] using wordTrace_append hprefix tailTrace_2529841
  have hstable : (prefixWord ++ tailWord_2529841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529841).length < 2 ^ (prefixWord ++ tailWord_2529841).sum := by decide
  have hdescent : baseEnd_2529841 < baseStart_2529841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529864 : List Nat := [2, 1, 3, 1, 1, 1, 1, 7, 6]
def baseStart_2529864 : Nat := 118140960795 + 2529864 * 2 ^ 59
def prefixEnd_2529864 : Nat := 4983230072969 + 3 ^ 40 * 2529864 * 2
def baseEnd_2529864 : Nat := 144337358056243903240597

theorem tailTrace_2529864 : CollatzResearch.WordTrace tailWord_2529864 prefixEnd_2529864 144337358056243903240597 := by
  unfold tailWord_2529864
  simp only [CollatzResearch.WordTrace]
  refine ⟨46135860253371134608874323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61514480337828179478499097 46135860253371134608874323)
  ·
    refine ⟨69203790380056701913311485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46135860253371134608874323 69203790380056701913311485)
    ·
      refine ⟨25951421392521263217491807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69203790380056701913311485 25951421392521263217491807)
      ·
        refine ⟨38927132088781894826237711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25951421392521263217491807 38927132088781894826237711)
        ·
          refine ⟨58390698133172842239356567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38927132088781894826237711 58390698133172842239356567)
          ·
            refine ⟨87586047199759263359034851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58390698133172842239356567 87586047199759263359034851)
            ·
              refine ⟨131379070799638895038552277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87586047199759263359034851 131379070799638895038552277)
              ·
                refine ⟨3079196971866536602466069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 131379070799638895038552277 3079196971866536602466069)
                ·
                  refine ⟨144337358056243903240597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3079196971866536602466069 144337358056243903240597)
                  ·
                    rfl

theorem cell23_2529864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 7, 6].length) (baseStart_2529864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2529864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2529864 prefixEnd_2529864 := by exact prefixLift 2529864
  have htrace : WordTrace (prefixWord ++ tailWord_2529864) baseStart_2529864 baseEnd_2529864 := by
    simpa [prefixWord, tailWord_2529864, baseEnd_2529864] using wordTrace_append hprefix tailTrace_2529864
  have hstable : (prefixWord ++ tailWord_2529864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529864).length < 2 ^ (prefixWord ++ tailWord_2529864).sum := by decide
  have hdescent : baseEnd_2529864 < baseStart_2529864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529902 : List Nat := [4, 1, 2, 2, 2, 2, 3, 2, 1, 4]
def baseStart_2529902 : Nat := 118140960795 + 2529902 * 2 ^ 59
def prefixEnd_2529902 : Nat := 4983230072969 + 3 ^ 40 * 2529902 * 2
def baseEnd_2529902 : Nat := 433018578257021993496733

theorem tailTrace_2529902 : CollatzResearch.WordTrace tailWord_2529902 prefixEnd_2529902 433018578257021993496733 := by
  unfold tailWord_2529902
  simp only [CollatzResearch.WordTrace]
  refine ⟨11534138310075575213453995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61515404320403067805087973 11534138310075575213453995)
  ·
    refine ⟨17301207465113362820180993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11534138310075575213453995 17301207465113362820180993)
    ·
      refine ⟨12975905598835022115135745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17301207465113362820180993 12975905598835022115135745)
      ·
        refine ⟨9731929199126266586351809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12975905598835022115135745 9731929199126266586351809)
        ·
          refine ⟨7298946899344699939763857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9731929199126266586351809 7298946899344699939763857)
          ·
            refine ⟨5474210174508524954822893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7298946899344699939763857 5474210174508524954822893)
            ·
              refine ⟨2052828815440696858058585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5474210174508524954822893 2052828815440696858058585)
              ·
                refine ⟨1539621611580522643543939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2052828815440696858058585 1539621611580522643543939)
                ·
                  refine ⟨2309432417370783965315909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1539621611580522643543939 2309432417370783965315909)
                  ·
                    refine ⟨433018578257021993496733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2309432417370783965315909 433018578257021993496733)
                    ·
                      rfl

theorem cell23_2529902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3, 2, 1, 4].length) (baseStart_2529902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2529902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2529902 prefixEnd_2529902 := by exact prefixLift 2529902
  have htrace : WordTrace (prefixWord ++ tailWord_2529902) baseStart_2529902 baseEnd_2529902 := by
    simpa [prefixWord, tailWord_2529902, baseEnd_2529902] using wordTrace_append hprefix tailTrace_2529902
  have hstable : (prefixWord ++ tailWord_2529902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529902).length < 2 ^ (prefixWord ++ tailWord_2529902).sum := by decide
  have hdescent : baseEnd_2529902 < baseStart_2529902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529931 : List Nat := [1, 1, 1, 1, 4, 1, 2, 6, 1, 1, 4]
def baseStart_2529931 : Nat := 118140960795 + 2529931 * 2 ^ 59
def prefixEnd_2529931 : Nat := 4983230072969 + 3 ^ 40 * 2529931 * 2
def baseEnd_2529931 : Nat := 1299070625710046367027565

theorem tailTrace_2529931 : CollatzResearch.WordTrace tailWord_2529931 prefixEnd_2529931 1299070625710046367027565 := by
  unfold tailWord_2529931
  simp only [CollatzResearch.WordTrace]
  refine ⟨92274164197499539660437647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61516109464999693106958431 92274164197499539660437647)
  ·
    refine ⟨138411246296249309490656471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92274164197499539660437647 138411246296249309490656471)
    ·
      refine ⟨207616869444373964235984707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138411246296249309490656471 207616869444373964235984707)
      ·
        refine ⟨311425304166560946353977061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207616869444373964235984707 311425304166560946353977061)
        ·
          refine ⟨58392244531230177441370699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 311425304166560946353977061 58392244531230177441370699)
          ·
            refine ⟨87588366796845266162056049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58392244531230177441370699 87588366796845266162056049)
            ·
              refine ⟨65691275097633949621542037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87588366796845266162056049 65691275097633949621542037)
              ·
                refine ⟨3079278520201591388509783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 65691275097633949621542037 3079278520201591388509783)
                ·
                  refine ⟨4618917780302387082764675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3079278520201591388509783 4618917780302387082764675)
                  ·
                    refine ⟨6928376670453580624147013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4618917780302387082764675 6928376670453580624147013)
                    ·
                      refine ⟨1299070625710046367027565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6928376670453580624147013 1299070625710046367027565)
                      ·
                        rfl

theorem cell23_2529931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 6, 1, 1, 4].length) (baseStart_2529931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2529931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2529931 prefixEnd_2529931 := by exact prefixLift 2529931
  have htrace : WordTrace (prefixWord ++ tailWord_2529931) baseStart_2529931 baseEnd_2529931 := by
    simpa [prefixWord, tailWord_2529931, baseEnd_2529931] using wordTrace_append hprefix tailTrace_2529931
  have hstable : (prefixWord ++ tailWord_2529931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529931).length < 2 ^ (prefixWord ++ tailWord_2529931).sum := by decide
  have hdescent : baseEnd_2529931 < baseStart_2529931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529954 : List Nat := [3, 3, 1, 16]
def baseStart_2529954 : Nat := 118140960795 + 2529954 * 2 ^ 59
def prefixEnd_2529954 : Nat := 4983230072969 + 3 ^ 40 * 2529954 * 2
def baseEnd_2529954 : Nat := 594002028241929481957

theorem tailTrace_2529954 : CollatzResearch.WordTrace tailWord_2529954 prefixEnd_2529954 594002028241929481957 := by
  unfold tailWord_2529954
  simp only [CollatzResearch.WordTrace]
  refine ⟨23068750769104053647131229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61516668717610809725683277 23068750769104053647131229)
  ·
    refine ⟨8650781538414020117674211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23068750769104053647131229 8650781538414020117674211)
    ·
      refine ⟨12976172307621030176511317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8650781538414020117674211 12976172307621030176511317)
      ·
        refine ⟨594002028241929481957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 16 12976172307621030176511317 594002028241929481957)
        ·
          rfl

theorem cell23_2529954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 16].length) (baseStart_2529954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2529954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2529954 prefixEnd_2529954 := by exact prefixLift 2529954
  have htrace : WordTrace (prefixWord ++ tailWord_2529954) baseStart_2529954 baseEnd_2529954 := by
    simpa [prefixWord, tailWord_2529954, baseEnd_2529954] using wordTrace_append hprefix tailTrace_2529954
  have hstable : (prefixWord ++ tailWord_2529954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529954).length < 2 ^ (prefixWord ++ tailWord_2529954).sum := by decide
  have hdescent : baseEnd_2529954 < baseStart_2529954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529959 : List Nat := [1, 1, 6, 3, 1, 1, 1, 4, 1, 1, 3]
def baseStart_2529959 : Nat := 118140960795 + 2529959 * 2 ^ 59
def prefixEnd_2529959 : Nat := 4983230072969 + 3 ^ 40 * 2529959 * 2
def baseEnd_2529959 : Nat := 1299085003168372257477437

theorem tailTrace_2529959 : CollatzResearch.WordTrace tailWord_2529959 prefixEnd_2529959 1299085003168372257477437 := by
  unfold tailWord_2529959
  simp only [CollatzResearch.WordTrace]
  refine ⟨92275185441398100442456931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61516790294265400294971287 92275185441398100442456931)
  ·
    refine ⟨138412778162097150663685397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92275185441398100442456931 138412778162097150663685397)
    ·
      refine ⟨6488098976348303937360253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 138412778162097150663685397 6488098976348303937360253)
      ·
        refine ⟨2433037116130613976510095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6488098976348303937360253 2433037116130613976510095)
        ·
          refine ⟨3649555674195920964765143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2433037116130613976510095 3649555674195920964765143)
          ·
            refine ⟨5474333511293881447147715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3649555674195920964765143 5474333511293881447147715)
            ·
              refine ⟨8211500266940822170721573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5474333511293881447147715 8211500266940822170721573)
              ·
                refine ⟨1539656300051404157010295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8211500266940822170721573 1539656300051404157010295)
                ·
                  refine ⟨2309484450077106235515443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1539656300051404157010295 2309484450077106235515443)
                  ·
                    refine ⟨3464226675115659353273165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2309484450077106235515443 3464226675115659353273165)
                    ·
                      refine ⟨1299085003168372257477437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3464226675115659353273165 1299085003168372257477437)
                      ·
                        rfl

theorem cell23_2529959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_2529959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2529959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2529959 prefixEnd_2529959 := by exact prefixLift 2529959
  have htrace : WordTrace (prefixWord ++ tailWord_2529959) baseStart_2529959 baseEnd_2529959 := by
    simpa [prefixWord, tailWord_2529959, baseEnd_2529959] using wordTrace_append hprefix tailTrace_2529959
  have hstable : (prefixWord ++ tailWord_2529959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529959).length < 2 ^ (prefixWord ++ tailWord_2529959).sum := by decide
  have hdescent : baseEnd_2529959 < baseStart_2529959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529971 : List Nat := [1, 1, 1, 2, 3, 6, 1, 8]
def baseStart_2529971 : Nat := 118140960795 + 2529971 * 2 ^ 59
def prefixEnd_2529971 : Nat := 4983230072969 + 3 ^ 40 * 2529971 * 2
def baseEnd_2529971 : Nat := 48114487590230600389903

theorem tailTrace_2529971 : CollatzResearch.WordTrace tailWord_2529971 prefixEnd_2529971 48114487590230600389903 := by
  unfold tailWord_2529971
  simp only [CollatzResearch.WordTrace]
  refine ⟨92275623117354626491893767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61517082078236417661262511 92275623117354626491893767)
  ·
    refine ⟨138413434676031939737840651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92275623117354626491893767 138413434676031939737840651)
    ·
      refine ⟨207620152014047909606760977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138413434676031939737840651 207620152014047909606760977)
      ·
        refine ⟨155715114010535932205070733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207620152014047909606760977 155715114010535932205070733)
        ·
          refine ⟨58393167753950974576901525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155715114010535932205070733 58393167753950974576901525)
          ·
            refine ⟨2737179738466451933292259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 58393167753950974576901525 2737179738466451933292259)
            ·
              refine ⟨4105769607699677899938389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2737179738466451933292259 4105769607699677899938389)
              ·
                refine ⟨48114487590230600389903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4105769607699677899938389 48114487590230600389903)
                ·
                  rfl

theorem cell23_2529971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 8].length) (baseStart_2529971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2529971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2529971 prefixEnd_2529971 := by exact prefixLift 2529971
  have htrace : WordTrace (prefixWord ++ tailWord_2529971) baseStart_2529971 baseEnd_2529971 := by
    simpa [prefixWord, tailWord_2529971, baseEnd_2529971] using wordTrace_append hprefix tailTrace_2529971
  have hstable : (prefixWord ++ tailWord_2529971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529971).length < 2 ^ (prefixWord ++ tailWord_2529971).sum := by decide
  have hdescent : baseEnd_2529971 < baseStart_2529971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529988 : List Nat := [2, 3, 3, 1, 1, 3, 3, 7]
def baseStart_2529988 : Nat := 118140960795 + 2529988 * 2 ^ 59
def prefixEnd_2529988 : Nat := 4983230072969 + 3 ^ 40 * 2529988 * 2
def baseEnd_2529988 : Nat := 48114810892864912741289

theorem tailTrace_2529988 : CollatzResearch.WordTrace tailWord_2529988 prefixEnd_2529988 48114810892864912741289 := by
  unfold tailWord_2529988
  simp only [CollatzResearch.WordTrace]
  refine ⟨46138121579146519197631309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61517495438862025596841745 46138121579146519197631309)
  ·
    refine ⟨17301795592179944699111741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46138121579146519197631309 17301795592179944699111741)
    ·
      refine ⟨6488173347067479262166903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17301795592179944699111741 6488173347067479262166903)
      ·
        refine ⟨9732260020601218893250355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6488173347067479262166903 9732260020601218893250355)
        ·
          refine ⟨14598390030901828339875533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9732260020601218893250355 14598390030901828339875533)
          ·
            refine ⟨5474396261588185627453325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14598390030901828339875533 5474396261588185627453325)
            ·
              refine ⟨2052898598095569610294997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5474396261588185627453325 2052898598095569610294997)
              ·
                refine ⟨48114810892864912741289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2052898598095569610294997 48114810892864912741289)
                ·
                  rfl

theorem cell23_2529988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3, 7].length) (baseStart_2529988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2529988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2529988 prefixEnd_2529988 := by exact prefixLift 2529988
  have htrace : WordTrace (prefixWord ++ tailWord_2529988) baseStart_2529988 baseEnd_2529988 := by
    simpa [prefixWord, tailWord_2529988, baseEnd_2529988] using wordTrace_append hprefix tailTrace_2529988
  have hstable : (prefixWord ++ tailWord_2529988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529988).length < 2 ^ (prefixWord ++ tailWord_2529988).sum := by decide
  have hdescent : baseEnd_2529988 < baseStart_2529988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529998 : List Nat := [4, 1, 1, 1, 3, 2, 2, 2, 1, 3, 3]
def baseStart_2529998 : Nat := 118140960795 + 2529998 * 2 ^ 59
def prefixEnd_2529998 : Nat := 4983230072969 + 3 ^ 40 * 2529998 * 2
def baseEnd_2529998 : Nat := 1299105028913897604889757

theorem tailTrace_2529998 : CollatzResearch.WordTrace tailWord_2529998 prefixEnd_2529998 1299105028913897604889757 := by
  unfold tailWord_2529998
  simp only [CollatzResearch.WordTrace]
  refine ⟨11534575986032101262890831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61517738592171206735417765 11534575986032101262890831)
  ·
    refine ⟨17301863979048151894336247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11534575986032101262890831 17301863979048151894336247)
    ·
      refine ⟨25952795968572227841504371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17301863979048151894336247 25952795968572227841504371)
      ·
        refine ⟨38929193952858341762256557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25952795968572227841504371 38929193952858341762256557)
        ·
          refine ⟨14598447732321878160846209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38929193952858341762256557 14598447732321878160846209)
          ·
            refine ⟨10948835799241408620634657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14598447732321878160846209 10948835799241408620634657)
            ·
              refine ⟨8211626849431056465475993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10948835799241408620634657 8211626849431056465475993)
              ·
                refine ⟨6158720137073292349106995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8211626849431056465475993 6158720137073292349106995)
                ·
                  refine ⟨9238080205609938523660493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6158720137073292349106995 9238080205609938523660493)
                  ·
                    refine ⟨3464280077103726946372685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9238080205609938523660493 3464280077103726946372685)
                    ·
                      refine ⟨1299105028913897604889757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3464280077103726946372685 1299105028913897604889757)
                      ·
                        rfl

theorem cell23_2529998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 2, 1, 3, 3].length) (baseStart_2529998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2529998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2529998 prefixEnd_2529998 := by exact prefixLift 2529998
  have htrace : WordTrace (prefixWord ++ tailWord_2529998) baseStart_2529998 baseEnd_2529998 := by
    simpa [prefixWord, tailWord_2529998, baseEnd_2529998] using wordTrace_append hprefix tailTrace_2529998
  have hstable : (prefixWord ++ tailWord_2529998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529998).length < 2 ^ (prefixWord ++ tailWord_2529998).sum := by decide
  have hdescent : baseEnd_2529998 < baseStart_2529998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530015 : List Nat := [1, 1, 2, 3, 2, 3, 3, 2, 2, 1, 3]
def baseStart_2530015 : Nat := 118140960795 + 2530015 * 2 ^ 59
def prefixEnd_2530015 : Nat := 4983230072969 + 3 ^ 40 * 2530015 * 2
def baseEnd_2530015 : Nat := 1299113758085024038377179

theorem tailTrace_2530015 : CollatzResearch.WordTrace tailWord_2530015 prefixEnd_2530015 1299113758085024038377179 := by
  unfold tailWord_2530015
  simp only [CollatzResearch.WordTrace]
  refine ⟨92277227929195222006495499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61518151952796814670996999 92277227929195222006495499)
  ·
    refine ⟨138415841893792833009743249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92277227929195222006495499 138415841893792833009743249)
    ·
      refine ⟨103811881420344624757307437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138415841893792833009743249 103811881420344624757307437)
      ·
        refine ⟨38929455532629234283990289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103811881420344624757307437 38929455532629234283990289)
        ·
          refine ⟨29197091649471925712992717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38929455532629234283990289 29197091649471925712992717)
          ·
            refine ⟨10948909368551972142372269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29197091649471925712992717 10948909368551972142372269)
            ·
              refine ⟨4105841013206989553389601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10948909368551972142372269 4105841013206989553389601)
              ·
                refine ⟨3079380759905242165042201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4105841013206989553389601 3079380759905242165042201)
                ·
                  refine ⟨2309535569928931623781651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3079380759905242165042201 2309535569928931623781651)
                  ·
                    refine ⟨3464303354893397435672477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2309535569928931623781651 3464303354893397435672477)
                    ·
                      refine ⟨1299113758085024038377179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3464303354893397435672477 1299113758085024038377179)
                      ·
                        rfl

theorem cell23_2530015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 2, 2, 1, 3].length) (baseStart_2530015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2530015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2530015 prefixEnd_2530015 := by exact prefixLift 2530015
  have htrace : WordTrace (prefixWord ++ tailWord_2530015) baseStart_2530015 baseEnd_2530015 := by
    simpa [prefixWord, tailWord_2530015, baseEnd_2530015] using wordTrace_append hprefix tailTrace_2530015
  have hstable : (prefixWord ++ tailWord_2530015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530015).length < 2 ^ (prefixWord ++ tailWord_2530015).sum := by decide
  have hdescent : baseEnd_2530015 < baseStart_2530015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530031 : List Nat := [1, 1, 2, 1, 5, 2, 2, 1, 2, 6]
def baseStart_2530031 : Nat := 118140960795 + 2530031 * 2 ^ 59
def prefixEnd_2530031 : Nat := 4983230072969 + 3 ^ 40 * 2530031 * 2
def baseEnd_2530031 : Nat := 433040657925165325259035

theorem tailTrace_2530031 : CollatzResearch.WordTrace tailWord_2530031 prefixEnd_2530031 433040657925165325259035 := by
  unfold tailWord_2530031
  simp only [CollatzResearch.WordTrace]
  refine ⟨92277811497137256739077947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61518540998091504492718631 92277811497137256739077947)
  ·
    refine ⟨138416717245705885108616921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92277811497137256739077947 138416717245705885108616921)
    ·
      refine ⟨103812537934279413831462691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138416717245705885108616921 103812537934279413831462691)
      ·
        refine ⟨155718806901419120747194037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103812537934279413831462691 155718806901419120747194037)
        ·
          refine ⟨14598638147008042570049441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 155718806901419120747194037 14598638147008042570049441)
          ·
            refine ⟨10948978610256031927537081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14598638147008042570049441 10948978610256031927537081)
            ·
              refine ⟨8211733957692023945652811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10948978610256031927537081 8211733957692023945652811)
              ·
                refine ⟨12317600936538035918479217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8211733957692023945652811 12317600936538035918479217)
                ·
                  refine ⟨9238200702403526938859413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12317600936538035918479217 9238200702403526938859413)
                  ·
                    refine ⟨433040657925165325259035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9238200702403526938859413 433040657925165325259035)
                    ·
                      rfl

theorem cell23_2530031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 2, 6].length) (baseStart_2530031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2530031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2530031 prefixEnd_2530031 := by exact prefixLift 2530031
  have htrace : WordTrace (prefixWord ++ tailWord_2530031) baseStart_2530031 baseEnd_2530031 := by
    simpa [prefixWord, tailWord_2530031, baseEnd_2530031] using wordTrace_append hprefix tailTrace_2530031
  have hstable : (prefixWord ++ tailWord_2530031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530031).length < 2 ^ (prefixWord ++ tailWord_2530031).sum := by decide
  have hdescent : baseEnd_2530031 < baseStart_2530031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530041 : List Nat := [1, 2, 1, 3, 1, 1, 1, 4, 2, 4, 3]
def baseStart_2530041 : Nat := 118140960795 + 2530041 * 2 ^ 59
def prefixEnd_2530041 : Nat := 4983230072969 + 3 ^ 40 * 2530041 * 2
def baseEnd_2530041 : Nat := 1299127108582040936652059

theorem tailTrace_2530041 : CollatzResearch.WordTrace tailWord_2530041 prefixEnd_2530041 1299127108582040936652059 := by
  unfold tailWord_2530041
  simp only [CollatzResearch.WordTrace]
  refine ⟨92278176227101028446941977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61518784151400685631294651 92278176227101028446941977)
  ·
    refine ⟨69208632170325771335206483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92278176227101028446941977 69208632170325771335206483)
    ·
      refine ⟨103812948255488657002809725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69208632170325771335206483 103812948255488657002809725)
      ·
        refine ⟨38929855595808246376053647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103812948255488657002809725 38929855595808246376053647)
        ·
          refine ⟨58394783393712369564080471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38929855595808246376053647 58394783393712369564080471)
          ·
            refine ⟨87592175090568554346120707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58394783393712369564080471 87592175090568554346120707)
            ·
              refine ⟨131388262635852831519181061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87592175090568554346120707 131388262635852831519181061)
              ·
                refine ⟨24635299244222405909846449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 131388262635852831519181061 24635299244222405909846449)
                ·
                  refine ⟨18476474433166804432384837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24635299244222405909846449 18476474433166804432384837)
                  ·
                    refine ⟨3464338956218775831072157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18476474433166804432384837 3464338956218775831072157)
                    ·
                      refine ⟨1299127108582040936652059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3464338956218775831072157 1299127108582040936652059)
                      ·
                        rfl

theorem cell23_2530041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 4, 3].length) (baseStart_2530041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2530041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2530041 prefixEnd_2530041 := by exact prefixLift 2530041
  have htrace : WordTrace (prefixWord ++ tailWord_2530041) baseStart_2530041 baseEnd_2530041 := by
    simpa [prefixWord, tailWord_2530041, baseEnd_2530041] using wordTrace_append hprefix tailTrace_2530041
  have hstable : (prefixWord ++ tailWord_2530041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530041).length < 2 ^ (prefixWord ++ tailWord_2530041).sum := by decide
  have hdescent : baseEnd_2530041 < baseStart_2530041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530088 : List Nat := [2, 1, 5, 1, 1, 1, 2, 1, 1, 5, 3]
def baseStart_2530088 : Nat := 118140960795 + 2530088 * 2 ^ 59
def prefixEnd_2530088 : Nat := 4983230072969 + 3 ^ 40 * 2530088 * 2
def baseEnd_2530088 : Nat := 1299151242172802252764343

theorem tailTrace_2530088 : CollatzResearch.WordTrace tailWord_2530088 prefixEnd_2530088 1299151242172802252764343 := by
  unfold tailWord_2530088
  simp only [CollatzResearch.WordTrace]
  refine ⟨46139945228965377736951459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61519926971953836982601945 46139945228965377736951459)
  ·
    refine ⟨69209917843448066605427189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46139945228965377736951459 69209917843448066605427189)
    ·
      refine ⟨6488429797823256244258799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 69209917843448066605427189 6488429797823256244258799)
      ·
        refine ⟨9732644696734884366388199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6488429797823256244258799 9732644696734884366388199)
        ·
          refine ⟨14598967045102326549582299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9732644696734884366388199 14598967045102326549582299)
          ·
            refine ⟨21898450567653489824373449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14598967045102326549582299 21898450567653489824373449)
            ·
              refine ⟨16423837925740117368280087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21898450567653489824373449 16423837925740117368280087)
              ·
                refine ⟨24635756888610176052420131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16423837925740117368280087 24635756888610176052420131)
                ·
                  refine ⟨36953635332915264078630197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24635756888610176052420131 36953635332915264078630197)
                  ·
                    refine ⟨3464403312460806007371581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36953635332915264078630197 3464403312460806007371581)
                    ·
                      refine ⟨1299151242172802252764343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3464403312460806007371581 1299151242172802252764343)
                      ·
                        rfl

theorem cell23_2530088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_2530088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2530088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2530088 prefixEnd_2530088 := by exact prefixLift 2530088
  have htrace : WordTrace (prefixWord ++ tailWord_2530088) baseStart_2530088 baseEnd_2530088 := by
    simpa [prefixWord, tailWord_2530088, baseEnd_2530088] using wordTrace_append hprefix tailTrace_2530088
  have hstable : (prefixWord ++ tailWord_2530088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530088).length < 2 ^ (prefixWord ++ tailWord_2530088).sum := by decide
  have hdescent : baseEnd_2530088 < baseStart_2530088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530093 : List Nat := [1, 5, 3, 2, 2, 1, 1, 2, 1, 3, 2]
def baseStart_2530093 : Nat := 118140960795 + 2530093 * 2 ^ 59
def prefixEnd_2530093 : Nat := 4983230072969 + 3 ^ 40 * 2530093 * 2
def baseEnd_2530093 : Nat := 1299153809576074733201821

theorem tailTrace_2530093 : CollatzResearch.WordTrace tailWord_2530093 prefixEnd_2530093 1299153809576074733201821 := by
  unfold tailWord_2530093
  simp only [CollatzResearch.WordTrace]
  refine ⟨92280072822912641327834933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61520048548608427551889955 92280072822912641327834933)
  ·
    refine ⟨8651256827148060124484525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 92280072822912641327834933 8651256827148060124484525)
    ·
      refine ⟨3244221310180522546681697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8651256827148060124484525 3244221310180522546681697)
      ·
        refine ⟨2433165982635391910011273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3244221310180522546681697 2433165982635391910011273)
        ·
          refine ⟨1824874486976543932508455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2433165982635391910011273 1824874486976543932508455)
          ·
            refine ⟨2737311730464815898762683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1824874486976543932508455 2737311730464815898762683)
            ·
              refine ⟨4105967595697223848144025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2737311730464815898762683 4105967595697223848144025)
              ·
                refine ⟨3079475696772917886108019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4105967595697223848144025 3079475696772917886108019)
                ·
                  refine ⟨4619213545159376829162029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3079475696772917886108019 4619213545159376829162029)
                  ·
                    refine ⟨1732205079434766310935761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4619213545159376829162029 1732205079434766310935761)
                    ·
                      refine ⟨1299153809576074733201821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1732205079434766310935761 1299153809576074733201821)
                      ·
                        rfl

theorem cell23_2530093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_2530093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2530093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2530093 prefixEnd_2530093 := by exact prefixLift 2530093
  have htrace : WordTrace (prefixWord ++ tailWord_2530093) baseStart_2530093 baseEnd_2530093 := by
    simpa [prefixWord, tailWord_2530093, baseEnd_2530093] using wordTrace_append hprefix tailTrace_2530093
  have hstable : (prefixWord ++ tailWord_2530093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530093).length < 2 ^ (prefixWord ++ tailWord_2530093).sum := by decide
  have hdescent : baseEnd_2530093 < baseStart_2530093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530128 : List Nat := [2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 4]
def baseStart_2530128 : Nat := 118140960795 + 2530128 * 2 ^ 59
def prefixEnd_2530128 : Nat := 4983230072969 + 3 ^ 40 * 2530128 * 2
def baseEnd_2530128 : Nat := 1299171781398982096264159

theorem tailTrace_2530128 : CollatzResearch.WordTrace tailWord_2530128 prefixEnd_2530128 1299171781398982096264159 := by
  unfold tailWord_2530128
  simp only [CollatzResearch.WordTrace]
  refine ⟨46140674688892921152679519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61520899585190561536906025 46140674688892921152679519)
  ·
    refine ⟨69211012033339381729019279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46140674688892921152679519 69211012033339381729019279)
    ·
      refine ⟨103816518050009072593528919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69211012033339381729019279 103816518050009072593528919)
      ·
        refine ⟨155724777075013608890293379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103816518050009072593528919 155724777075013608890293379)
        ·
          refine ⟨233587165612520413335440069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155724777075013608890293379 233587165612520413335440069)
          ·
            refine ⟨43797593552347577500395013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 233587165612520413335440069 43797593552347577500395013)
            ·
              refine ⟨8212048791065170781324065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43797593552347577500395013 8212048791065170781324065)
              ·
                refine ⟨6159036593298878085993049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8212048791065170781324065 6159036593298878085993049)
                ·
                  refine ⟨4619277444974158564494787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6159036593298878085993049 4619277444974158564494787)
                  ·
                    refine ⟨6928916167461237846742181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4619277444974158564494787 6928916167461237846742181)
                    ·
                      refine ⟨1299171781398982096264159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6928916167461237846742181 1299171781398982096264159)
                      ·
                        rfl

theorem cell23_2530128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 4].length) (baseStart_2530128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2530128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2530128 prefixEnd_2530128 := by exact prefixLift 2530128
  have htrace : WordTrace (prefixWord ++ tailWord_2530128) baseStart_2530128 baseEnd_2530128 := by
    simpa [prefixWord, tailWord_2530128, baseEnd_2530128] using wordTrace_append hprefix tailTrace_2530128
  have hstable : (prefixWord ++ tailWord_2530128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530128).length < 2 ^ (prefixWord ++ tailWord_2530128).sum := by decide
  have hdescent : baseEnd_2530128 < baseStart_2530128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530129 : List Nat := [1, 2, 2, 1, 7, 1, 2, 2, 5]
def baseStart_2530129 : Nat := 118140960795 + 2530129 * 2 ^ 59
def prefixEnd_2530129 : Nat := 4983230072969 + 3 ^ 40 * 2530129 * 2
def baseEnd_2530129 : Nat := 144352477208848510261295

theorem tailTrace_2530129 : CollatzResearch.WordTrace tailWord_2530129 prefixEnd_2530129 144352477208848510261295 := by
  unfold tailWord_2530129
  simp only [CollatzResearch.WordTrace]
  refine ⟨92281385850782219476145441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61520923900521479650763627 92281385850782219476145441)
  ·
    refine ⟨69211039388086664607109081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92281385850782219476145441 69211039388086664607109081)
    ·
      refine ⟨51908279541064998455331811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69211039388086664607109081 51908279541064998455331811)
      ·
        refine ⟨77862419311597497682997717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51908279541064998455331811 77862419311597497682997717)
        ·
          refine ⟨1824900452615566351945259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 77862419311597497682997717 1824900452615566351945259)
          ·
            refine ⟨2737350678923349527917889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1824900452615566351945259 2737350678923349527917889)
            ·
              refine ⟨2053013009192512145938417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2737350678923349527917889 2053013009192512145938417)
              ·
                refine ⟨1539759756894384109453813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2053013009192512145938417 1539759756894384109453813)
                ·
                  refine ⟨144352477208848510261295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1539759756894384109453813 144352477208848510261295)
                  ·
                    rfl

theorem cell23_2530129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 2, 2, 5].length) (baseStart_2530129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2530129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2530129 prefixEnd_2530129 := by exact prefixLift 2530129
  have htrace : WordTrace (prefixWord ++ tailWord_2530129) baseStart_2530129 baseEnd_2530129 := by
    simpa [prefixWord, tailWord_2530129, baseEnd_2530129] using wordTrace_append hprefix tailTrace_2530129
  have hstable : (prefixWord ++ tailWord_2530129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530129).length < 2 ^ (prefixWord ++ tailWord_2530129).sum := by decide
  have hdescent : baseEnd_2530129 < baseStart_2530129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530165 : List Nat := [1, 3, 4, 1, 1, 3, 1, 1, 1, 4, 3]
def baseStart_2530165 : Nat := 118140960795 + 2530165 * 2 ^ 59
def prefixEnd_2530165 : Nat := 4983230072969 + 3 ^ 40 * 2530165 * 2
def baseEnd_2530165 : Nat := 1299190780183198451501489

theorem tailTrace_2530165 : CollatzResearch.WordTrace tailWord_2530165 prefixEnd_2530165 1299190780183198451501489 := by
  unfold tailWord_2530165
  simp only [CollatzResearch.WordTrace]
  refine ⟨92282698878651797624455949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61521799252434531749637299 92282698878651797624455949)
  ·
    refine ⟨34606012079494424109170981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92282698878651797624455949 34606012079494424109170981)
    ·
      refine ⟨6488627264905204520469559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34606012079494424109170981 6488627264905204520469559)
      ·
        refine ⟨9732940897357806780704339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6488627264905204520469559 9732940897357806780704339)
        ·
          refine ⟨14599411346036710171056509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9732940897357806780704339 14599411346036710171056509)
          ·
            refine ⟨5474779254763766314146191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14599411346036710171056509 5474779254763766314146191)
            ·
              refine ⟨8212168882145649471219287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5474779254763766314146191 8212168882145649471219287)
              ·
                refine ⟨12318253323218474206828931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8212168882145649471219287 12318253323218474206828931)
                ·
                  refine ⟨18477379984827711310243397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12318253323218474206828931 18477379984827711310243397)
                  ·
                    refine ⟨3464508747155195870670637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18477379984827711310243397 3464508747155195870670637)
                    ·
                      refine ⟨1299190780183198451501489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3464508747155195870670637 1299190780183198451501489)
                      ·
                        rfl

theorem cell23_2530165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_2530165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2530165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2530165 prefixEnd_2530165 := by exact prefixLift 2530165
  have htrace : WordTrace (prefixWord ++ tailWord_2530165) baseStart_2530165 baseEnd_2530165 := by
    simpa [prefixWord, tailWord_2530165, baseEnd_2530165] using wordTrace_append hprefix tailTrace_2530165
  have hstable : (prefixWord ++ tailWord_2530165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530165).length < 2 ^ (prefixWord ++ tailWord_2530165).sum := by decide
  have hdescent : baseEnd_2530165 < baseStart_2530165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
